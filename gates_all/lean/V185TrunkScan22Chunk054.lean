import V185TrunkScan22Chunk053

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_485655 : List Nat := [1, 1, 3, 4, 1, 2, 1, 5, 1, 3]
def baseStart_485655 : Nat := 118140960795 + 485655 * 2 ^ 59
def prefixEnd_485655 : Nat := 4983230072969 + 3 ^ 40 * 485655 * 2
def baseEnd_485655 : Nat := 166249631506268404186013

theorem tailTrace_485655 : CollatzResearch.WordTrace tailWord_485655 prefixEnd_485655 166249631506268404186013 := by
  unfold tailWord_485655
  simp only [CollatzResearch.WordTrace]
  refine ⟨17713293055562353115658419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11808862037041568743772279 17713293055562353115658419)
  ·
    refine ⟨26569939583343529673487629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17713293055562353115658419 26569939583343529673487629)
    ·
      refine ⟨9963727343753823627557861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26569939583343529673487629 9963727343753823627557861)
      ·
        refine ⟨1868198876953841930167099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9963727343753823627557861 1868198876953841930167099)
        ·
          refine ⟨2802298315430762895250649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1868198876953841930167099 2802298315430762895250649)
          ·
            refine ⟨2101723736573072171437987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2802298315430762895250649 2101723736573072171437987)
            ·
              refine ⟨3152585604859608257156981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2101723736573072171437987 3152585604859608257156981)
              ·
                refine ⟨295554900455588274108467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3152585604859608257156981 295554900455588274108467)
                ·
                  refine ⟨443332350683382411162701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 295554900455588274108467 443332350683382411162701)
                  ·
                    refine ⟨166249631506268404186013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 443332350683382411162701 166249631506268404186013)
                    ·
                      rfl

theorem cell22_485655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 5, 1, 3].length) (baseStart_485655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_485655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_485655 prefixEnd_485655 := by exact prefixLift 485655
  have htrace : WordTrace (prefixWord ++ tailWord_485655) baseStart_485655 baseEnd_485655 := by
    simpa [prefixWord, tailWord_485655, baseEnd_485655] using wordTrace_append hprefix tailTrace_485655
  have hstable : (prefixWord ++ tailWord_485655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485655).length < 2 ^ (prefixWord ++ tailWord_485655).sum := by decide
  have hdescent : baseEnd_485655 < baseStart_485655 := by decide
  rcases family_descends (prefixWord ++ tailWord_485655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485668 : List Nat := [2, 3, 1, 3, 1, 2, 3, 2, 5]
def baseStart_485668 : Nat := 118140960795 + 485668 * 2 ^ 59
def prefixEnd_485668 : Nat := 4983230072969 + 3 ^ 40 * 485668 * 2
def baseEnd_485668 : Nat := 55418027223980234536991

theorem tailTrace_485668 : CollatzResearch.WordTrace tailWord_485668 prefixEnd_485668 55418027223980234536991 := by
  unfold tailWord_485668
  simp only [CollatzResearch.WordTrace]
  refine ⟨8856883602257628167940829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11809178136343504223921105 8856883602257628167940829)
  ·
    refine ⟨3321331350846610562977811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8856883602257628167940829 3321331350846610562977811)
    ·
      refine ⟨4981997026269915844466717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3321331350846610562977811 4981997026269915844466717)
      ·
        refine ⟨1868248884851218441675019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4981997026269915844466717 1868248884851218441675019)
        ·
          refine ⟨2802373327276827662512529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1868248884851218441675019 2802373327276827662512529)
          ·
            refine ⟨2101779995457620746884397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2802373327276827662512529 2101779995457620746884397)
            ·
              refine ⟨788167498296607780081649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2101779995457620746884397 788167498296607780081649)
              ·
                refine ⟨591125623722455835061237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 788167498296607780081649 591125623722455835061237)
                ·
                  refine ⟨55418027223980234536991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 591125623722455835061237 55418027223980234536991)
                  ·
                    rfl

theorem cell22_485668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 2, 5].length) (baseStart_485668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_485668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_485668 prefixEnd_485668 := by exact prefixLift 485668
  have htrace : WordTrace (prefixWord ++ tailWord_485668) baseStart_485668 baseEnd_485668 := by
    simpa [prefixWord, tailWord_485668, baseEnd_485668] using wordTrace_append hprefix tailTrace_485668
  have hstable : (prefixWord ++ tailWord_485668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485668).length < 2 ^ (prefixWord ++ tailWord_485668).sum := by decide
  have hdescent : baseEnd_485668 < baseStart_485668 := by decide
  rcases family_descends (prefixWord ++ tailWord_485668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485730 : List Nat := [3, 3, 2, 1, 1, 4, 1, 1, 6]
def baseStart_485730 : Nat := 118140960795 + 485730 * 2 ^ 59
def prefixEnd_485730 : Nat := 4983230072969 + 3 ^ 40 * 485730 * 2
def baseEnd_485730 : Nat := 55425101846331069520261

theorem tailTrace_485730 : CollatzResearch.WordTrace tailWord_485730 prefixEnd_485730 55425101846331069520261 := by
  unfold tailWord_485730
  simp only [CollatzResearch.WordTrace]
  refine ⟨4429007132572660231159661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11810685686860427283092429 4429007132572660231159661)
  ·
    refine ⟨1660877674714747586684873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4429007132572660231159661 1660877674714747586684873)
    ·
      refine ⟨1245658256036060690013655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1660877674714747586684873 1245658256036060690013655)
      ·
        refine ⟨1868487384054091035020483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1245658256036060690013655 1868487384054091035020483)
        ·
          refine ⟨2802731076081136552530725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1868487384054091035020483 2802731076081136552530725)
          ·
            refine ⟨525512076765213103599511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2802731076081136552530725 525512076765213103599511)
            ·
              refine ⟨788268115147819655399267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 525512076765213103599511 788268115147819655399267)
              ·
                refine ⟨1182402172721729483098901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 788268115147819655399267 1182402172721729483098901)
                ·
                  refine ⟨55425101846331069520261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1182402172721729483098901 55425101846331069520261)
                  ·
                    rfl

theorem cell22_485730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_485730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_485730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_485730 prefixEnd_485730 := by exact prefixLift 485730
  have htrace : WordTrace (prefixWord ++ tailWord_485730) baseStart_485730 baseEnd_485730 := by
    simpa [prefixWord, tailWord_485730, baseEnd_485730] using wordTrace_append hprefix tailTrace_485730
  have hstable : (prefixWord ++ tailWord_485730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485730).length < 2 ^ (prefixWord ++ tailWord_485730).sum := by decide
  have hdescent : baseEnd_485730 < baseStart_485730 := by decide
  rcases family_descends (prefixWord ++ tailWord_485730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485762 : List Nat := [3, 4, 2, 1, 2, 1, 1, 2, 1, 5]
def baseStart_485762 : Nat := 118140960795 + 485762 * 2 ^ 59
def prefixEnd_485762 : Nat := 4983230072969 + 3 ^ 40 * 485762 * 2
def baseEnd_485762 : Nat := 166286259792955791760685

theorem tailTrace_485762 : CollatzResearch.WordTrace tailWord_485762 prefixEnd_485762 166286259792955791760685 := by
  unfold tailWord_485762
  simp only [CollatzResearch.WordTrace]
  refine ⟨4429298916543677597450885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11811463777449806926535693 4429298916543677597450885)
  ·
    refine ⟨830493546851939549522041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4429298916543677597450885 830493546851939549522041)
    ·
      refine ⟨622870160138954662141531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 830493546851939549522041 622870160138954662141531)
      ·
        refine ⟨934305240208431993212297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 622870160138954662141531 934305240208431993212297)
        ·
          refine ⟨700728930156323994909223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 934305240208431993212297 700728930156323994909223)
          ·
            refine ⟨1051093395234485992363835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 700728930156323994909223 1051093395234485992363835)
            ·
              refine ⟨1576640092851728988545753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1051093395234485992363835 1576640092851728988545753)
              ·
                refine ⟨1182480069638796741409315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1576640092851728988545753 1182480069638796741409315)
                ·
                  refine ⟨1773720104458195112113973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1182480069638796741409315 1773720104458195112113973)
                  ·
                    refine ⟨166286259792955791760685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1773720104458195112113973 166286259792955791760685)
                    ·
                      rfl

theorem cell22_485762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_485762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_485762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_485762 prefixEnd_485762 := by exact prefixLift 485762
  have htrace : WordTrace (prefixWord ++ tailWord_485762) baseStart_485762 baseEnd_485762 := by
    simpa [prefixWord, tailWord_485762, baseEnd_485762] using wordTrace_append hprefix tailTrace_485762
  have hstable : (prefixWord ++ tailWord_485762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485762).length < 2 ^ (prefixWord ++ tailWord_485762).sum := by decide
  have hdescent : baseEnd_485762 < baseStart_485762 := by decide
  rcases family_descends (prefixWord ++ tailWord_485762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485925 : List Nat := [1, 3, 1, 2, 2, 1, 2, 4, 3, 3]
def baseStart_485925 : Nat := 118140960795 + 485925 * 2 ^ 59
def prefixEnd_485925 : Nat := 4983230072969 + 3 ^ 40 * 485925 * 2
def baseEnd_485925 : Nat := 166342058024077699935185

theorem tailTrace_485925 : CollatzResearch.WordTrace tailWord_485925 prefixEnd_485925 166342058024077699935185 := by
  unfold tailWord_485925
  simp only [CollatzResearch.WordTrace]
  refine ⟨17723140764584189227987229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11815427176389459485324819 17723140764584189227987229)
  ·
    refine ⟨6646177786719070960495211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17723140764584189227987229 6646177786719070960495211)
    ·
      refine ⟨9969266680078606440742817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6646177786719070960495211 9969266680078606440742817)
      ·
        refine ⟨7476950010058954830557113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9969266680078606440742817 7476950010058954830557113)
        ·
          refine ⟨5607712507544216122917835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7476950010058954830557113 5607712507544216122917835)
          ·
            refine ⟨8411568761316324184376753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5607712507544216122917835 8411568761316324184376753)
            ·
              refine ⟨6308676570987243138282565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8411568761316324184376753 6308676570987243138282565)
              ·
                refine ⟨1182876857060108088427981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6308676570987243138282565 1182876857060108088427981)
                ·
                  refine ⟨443578821397540533160493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1182876857060108088427981 443578821397540533160493)
                  ·
                    refine ⟨166342058024077699935185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 443578821397540533160493 166342058024077699935185)
                    ·
                      rfl

theorem cell22_485925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 4, 3, 3].length) (baseStart_485925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_485925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_485925 prefixEnd_485925 := by exact prefixLift 485925
  have htrace : WordTrace (prefixWord ++ tailWord_485925) baseStart_485925 baseEnd_485925 := by
    simpa [prefixWord, tailWord_485925, baseEnd_485925] using wordTrace_append hprefix tailTrace_485925
  have hstable : (prefixWord ++ tailWord_485925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485925).length < 2 ^ (prefixWord ++ tailWord_485925).sum := by decide
  have hdescent : baseEnd_485925 < baseStart_485925 := by decide
  rcases family_descends (prefixWord ++ tailWord_485925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485938 : List Nat := [3, 2, 1, 1, 2, 1, 2, 1, 9]
def baseStart_485938 : Nat := 118140960795 + 485938 * 2 ^ 59
def prefixEnd_485938 : Nat := 4983230072969 + 3 ^ 40 * 485938 * 2
def baseEnd_485938 : Nat := 55448836063249999786715

theorem tailTrace_485938 : CollatzResearch.WordTrace tailWord_485938 prefixEnd_485938 55448836063249999786715 := by
  unfold tailWord_485938
  simp only [CollatzResearch.WordTrace]
  refine ⟨4430903728384273112052617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11815743275691394965473645 4430903728384273112052617)
  ·
    refine ⟨3323177796288204834039463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4430903728384273112052617 3323177796288204834039463)
    ·
      refine ⟨4984766694432307251059195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3323177796288204834039463 4984766694432307251059195)
      ·
        refine ⟨7477150041648460876588793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4984766694432307251059195 7477150041648460876588793)
        ·
          refine ⟨5607862531236345657441595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7477150041648460876588793 5607862531236345657441595)
          ·
            refine ⟨8411793796854518486162393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5607862531236345657441595 8411793796854518486162393)
            ·
              refine ⟨6308845347640888864621795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8411793796854518486162393 6308845347640888864621795)
              ·
                refine ⟨9463268021461333296932693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6308845347640888864621795 9463268021461333296932693)
                ·
                  refine ⟨55448836063249999786715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 9463268021461333296932693 55448836063249999786715)
                  ·
                    rfl

theorem cell22_485938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 9].length) (baseStart_485938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_485938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_485938 prefixEnd_485938 := by exact prefixLift 485938
  have htrace : WordTrace (prefixWord ++ tailWord_485938) baseStart_485938 baseEnd_485938 := by
    simpa [prefixWord, tailWord_485938, baseEnd_485938] using wordTrace_append hprefix tailTrace_485938
  have hstable : (prefixWord ++ tailWord_485938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485938).length < 2 ^ (prefixWord ++ tailWord_485938).sum := by decide
  have hdescent : baseEnd_485938 < baseStart_485938 := by decide
  rcases family_descends (prefixWord ++ tailWord_485938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485959 : List Nat := [1, 1, 4, 1, 4, 2, 1, 4, 1, 3]
def baseStart_485959 : Nat := 118140960795 + 485959 * 2 ^ 59
def prefixEnd_485959 : Nat := 4983230072969 + 3 ^ 40 * 485959 * 2
def baseEnd_485959 : Nat := 166353696918912944585081

theorem tailTrace_485959 : CollatzResearch.WordTrace tailWord_485959 prefixEnd_485959 166353696918912944585081 := by
  unfold tailWord_485959
  simp only [CollatzResearch.WordTrace]
  refine ⟨17724380846461013034724931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11816253897640675356483287 17724380846461013034724931)
  ·
    refine ⟨26586571269691519552087397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17724380846461013034724931 26586571269691519552087397)
    ·
      refine ⟨4984982113067159916016387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26586571269691519552087397 4984982113067159916016387)
      ·
        refine ⟨7477473169600739874024581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4984982113067159916016387 7477473169600739874024581)
        ·
          refine ⟨1402026219300138726379609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7477473169600739874024581 1402026219300138726379609)
          ·
            refine ⟨1051519664475104044784707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1402026219300138726379609 1051519664475104044784707)
            ·
              refine ⟨1577279496712656067177061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1051519664475104044784707 1577279496712656067177061)
              ·
                refine ⟨295739905633623012595699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1577279496712656067177061 295739905633623012595699)
                ·
                  refine ⟨443609858450434518893549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 295739905633623012595699 443609858450434518893549)
                  ·
                    refine ⟨166353696918912944585081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 443609858450434518893549 166353696918912944585081)
                    ·
                      rfl

theorem cell22_485959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 4, 1, 3].length) (baseStart_485959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_485959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_485959 prefixEnd_485959 := by exact prefixLift 485959
  have htrace : WordTrace (prefixWord ++ tailWord_485959) baseStart_485959 baseEnd_485959 := by
    simpa [prefixWord, tailWord_485959, baseEnd_485959] using wordTrace_append hprefix tailTrace_485959
  have hstable : (prefixWord ++ tailWord_485959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485959).length < 2 ^ (prefixWord ++ tailWord_485959).sum := by decide
  have hdescent : baseEnd_485959 < baseStart_485959 := by decide
  rcases family_descends (prefixWord ++ tailWord_485959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485970 : List Nat := [3, 2, 2, 1, 2, 1, 3, 1, 2, 5]
def baseStart_485970 : Nat := 118140960795 + 485970 * 2 ^ 59
def prefixEnd_485970 : Nat := 4983230072969 + 3 ^ 40 * 485970 * 2
def baseEnd_485970 : Nat := 166357462443712582560047

theorem tailTrace_485970 : CollatzResearch.WordTrace tailWord_485970 prefixEnd_485970 166357462443712582560047 := by
  unfold tailWord_485970
  simp only [CollatzResearch.WordTrace]
  refine ⟨4431195512355290478343841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11816521366280774608916909 4431195512355290478343841)
  ·
    refine ⟨3323396634266467858757881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4431195512355290478343841 3323396634266467858757881)
    ·
      refine ⟨2492547475699850894068411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3323396634266467858757881 2492547475699850894068411)
      ·
        refine ⟨3738821213549776341102617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2492547475699850894068411 3738821213549776341102617)
        ·
          refine ⟨2804115910162332255826963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3738821213549776341102617 2804115910162332255826963)
          ·
            refine ⟨4206173865243498383740445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2804115910162332255826963 4206173865243498383740445)
            ·
              refine ⟨1577315199466311893902667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4206173865243498383740445 1577315199466311893902667)
              ·
                refine ⟨2365972799199467840854001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1577315199466311893902667 2365972799199467840854001)
                ·
                  refine ⟨1774479599399600880640501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2365972799199467840854001 1774479599399600880640501)
                  ·
                    refine ⟨166357462443712582560047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1774479599399600880640501 166357462443712582560047)
                    ·
                      rfl

theorem cell22_485970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_485970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_485970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_485970 prefixEnd_485970 := by exact prefixLift 485970
  have htrace : WordTrace (prefixWord ++ tailWord_485970) baseStart_485970 baseEnd_485970 := by
    simpa [prefixWord, tailWord_485970, baseEnd_485970] using wordTrace_append hprefix tailTrace_485970
  have hstable : (prefixWord ++ tailWord_485970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485970).length < 2 ^ (prefixWord ++ tailWord_485970).sum := by decide
  have hdescent : baseEnd_485970 < baseStart_485970 := by decide
  rcases family_descends (prefixWord ++ tailWord_485970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485985 : List Nat := [1, 2, 3, 1, 1, 4, 2, 1, 3, 4]
def baseStart_485985 : Nat := 118140960795 + 485985 * 2 ^ 59
def prefixEnd_485985 : Nat := 4983230072969 + 3 ^ 40 * 485985 * 2
def baseEnd_485985 : Nat := 166362597250257543435001

theorem tailTrace_485985 : CollatzResearch.WordTrace tailWord_485985 prefixEnd_485985 166362597250257543435001 := by
  unfold tailWord_485985
  simp only [CollatzResearch.WordTrace]
  refine ⟨17725329144366819475171409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11816886096244546316780939 17725329144366819475171409)
  ·
    refine ⟨13293996858275114606378557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17725329144366819475171409 13293996858275114606378557)
    ·
      refine ⟨4985248821853167977391959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13293996858275114606378557 4985248821853167977391959)
      ·
        refine ⟨7477873232779751966087939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4985248821853167977391959 7477873232779751966087939)
        ·
          refine ⟨11216809849169627949131909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7477873232779751966087939 11216809849169627949131909)
          ·
            refine ⟨2103151846719305240462233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11216809849169627949131909 2103151846719305240462233)
            ·
              refine ⟨1577363885039478930346675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2103151846719305240462233 1577363885039478930346675)
              ·
                refine ⟨2366045827559218395520013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1577363885039478930346675 2366045827559218395520013)
                ·
                  refine ⟨887267185334706898320005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2366045827559218395520013 887267185334706898320005)
                  ·
                    refine ⟨166362597250257543435001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 887267185334706898320005 166362597250257543435001)
                    ·
                      rfl

theorem cell22_485985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_485985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_485985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_485985 prefixEnd_485985 := by exact prefixLift 485985
  have htrace : WordTrace (prefixWord ++ tailWord_485985) baseStart_485985 baseEnd_485985 := by
    simpa [prefixWord, tailWord_485985, baseEnd_485985] using wordTrace_append hprefix tailTrace_485985
  have hstable : (prefixWord ++ tailWord_485985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485985).length < 2 ^ (prefixWord ++ tailWord_485985).sum := by decide
  have hdescent : baseEnd_485985 < baseStart_485985 := by decide
  rcases family_descends (prefixWord ++ tailWord_485985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486006 : List Nat := [5, 1, 1, 2, 4, 1, 1, 2, 5]
def baseStart_486006 : Nat := 118140960795 + 486006 * 2 ^ 59
def prefixEnd_486006 : Nat := 4983230072969 + 3 ^ 40 * 486006 * 2
def baseEnd_486006 : Nat := 55456595326473496219979

theorem tailTrace_486006 : CollatzResearch.WordTrace tailWord_486006 prefixEnd_486006 55456595326473496219979 := by
  unfold tailWord_486006
  simp only [CollatzResearch.WordTrace]
  refine ⟨1107880942330671253855367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11817396718193826707790581 1107880942330671253855367)
  ·
    refine ⟨1661821413496006880783051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1107880942330671253855367 1661821413496006880783051)
    ·
      refine ⟨2492732120244010321174577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1661821413496006880783051 2492732120244010321174577)
      ·
        refine ⟨1869549090183007740880933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2492732120244010321174577 1869549090183007740880933)
        ·
          refine ⟨350540454409313951415175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1869549090183007740880933 350540454409313951415175)
          ·
            refine ⟨525810681613970927122763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350540454409313951415175 525810681613970927122763)
            ·
              refine ⟨788716022420956390684145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 525810681613970927122763 788716022420956390684145)
              ·
                refine ⟨591537016815717293013109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 788716022420956390684145 591537016815717293013109)
                ·
                  refine ⟨55456595326473496219979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 591537016815717293013109 55456595326473496219979)
                  ·
                    rfl

theorem cell22_486006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_486006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_486006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_486006 prefixEnd_486006 := by exact prefixLift 486006
  have htrace : WordTrace (prefixWord ++ tailWord_486006) baseStart_486006 baseEnd_486006 := by
    simpa [prefixWord, tailWord_486006, baseEnd_486006] using wordTrace_append hprefix tailTrace_486006
  have hstable : (prefixWord ++ tailWord_486006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486006).length < 2 ^ (prefixWord ++ tailWord_486006).sum := by decide
  have hdescent : baseEnd_486006 < baseStart_486006 := by decide
  rcases family_descends (prefixWord ++ tailWord_486006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486017 : List Nat := [1, 2, 4, 2, 1, 1, 1, 6, 4]
def baseStart_486017 : Nat := 118140960795 + 486017 * 2 ^ 59
def prefixEnd_486017 : Nat := 4983230072969 + 3 ^ 40 * 486017 * 2
def baseEnd_486017 : Nat := 55457850501406708878301

theorem tailTrace_486017 : CollatzResearch.WordTrace tailWord_486017 prefixEnd_486017 55457850501406708878301 := by
  unfold tailWord_486017
  simp only [CollatzResearch.WordTrace]
  refine ⟨17726496280250888940336305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11817664186833925960224203 17726496280250888940336305)
  ·
    refine ⟨13294872210188166705252229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17726496280250888940336305 13294872210188166705252229)
    ·
      refine ⟨2492788539410281257234793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13294872210188166705252229 2492788539410281257234793)
      ·
        refine ⟨1869591404557710942926095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2492788539410281257234793 1869591404557710942926095)
        ·
          refine ⟨2804387106836566414389143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1869591404557710942926095 2804387106836566414389143)
          ·
            refine ⟨4206580660254849621583715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2804387106836566414389143 4206580660254849621583715)
            ·
              refine ⟨6309870990382274432375573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4206580660254849621583715 6309870990382274432375573)
              ·
                refine ⟨295775202674169114017605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6309870990382274432375573 295775202674169114017605)
                ·
                  refine ⟨55457850501406708878301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 295775202674169114017605 55457850501406708878301)
                  ·
                    rfl

theorem cell22_486017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 6, 4].length) (baseStart_486017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_486017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_486017 prefixEnd_486017 := by exact prefixLift 486017
  have htrace : WordTrace (prefixWord ++ tailWord_486017) baseStart_486017 baseEnd_486017 := by
    simpa [prefixWord, tailWord_486017, baseEnd_486017] using wordTrace_append hprefix tailTrace_486017
  have hstable : (prefixWord ++ tailWord_486017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486017).length < 2 ^ (prefixWord ++ tailWord_486017).sum := by decide
  have hdescent : baseEnd_486017 < baseStart_486017 := by decide
  rcases family_descends (prefixWord ++ tailWord_486017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486030 : List Nat := [4, 1, 1, 3, 1, 1, 1, 1, 3, 6]
def baseStart_486030 : Nat := 118140960795 + 486030 * 2 ^ 59
def prefixEnd_486030 : Nat := 4983230072969 + 3 ^ 40 * 486030 * 2
def baseEnd_486030 : Nat := 166378001669892426059863

theorem tailTrace_486030 : CollatzResearch.WordTrace tailWord_486030 prefixEnd_486030 166378001669892426059863 := by
  unfold tailWord_486030
  simp only [CollatzResearch.WordTrace]
  refine ⟨2215871303650474020069943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11817980286135861440373029 2215871303650474020069943)
  ·
    refine ⟨3323806955475711030104915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2215871303650474020069943 3323806955475711030104915)
    ·
      refine ⟨4985710433213566545157373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3323806955475711030104915 4985710433213566545157373)
      ·
        refine ⟨1869641412455087454434015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4985710433213566545157373 1869641412455087454434015)
        ·
          refine ⟨2804462118682631181651023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1869641412455087454434015 2804462118682631181651023)
          ·
            refine ⟨4206693178023946772476535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2804462118682631181651023 4206693178023946772476535)
            ·
              refine ⟨6310039767035920158714803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4206693178023946772476535 6310039767035920158714803)
              ·
                refine ⟨9465059650553880238072205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6310039767035920158714803 9465059650553880238072205)
                ·
                  refine ⟨3549397368957705089277077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9465059650553880238072205 3549397368957705089277077)
                  ·
                    refine ⟨166378001669892426059863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3549397368957705089277077 166378001669892426059863)
                    ·
                      rfl

theorem cell22_486030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_486030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_486030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_486030 prefixEnd_486030 := by exact prefixLift 486030
  have htrace : WordTrace (prefixWord ++ tailWord_486030) baseStart_486030 baseEnd_486030 := by
    simpa [prefixWord, tailWord_486030, baseEnd_486030] using wordTrace_append hprefix tailTrace_486030
  have hstable : (prefixWord ++ tailWord_486030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486030).length < 2 ^ (prefixWord ++ tailWord_486030).sum := by decide
  have hdescent : baseEnd_486030 < baseStart_486030 := by decide
  rcases family_descends (prefixWord ++ tailWord_486030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486062 : List Nat := [4, 1, 4, 1, 1, 1, 10]
def baseStart_486062 : Nat := 118140960795 + 486062 * 2 ^ 59
def prefixEnd_486062 : Nat := 4983230072969 + 3 ^ 40 * 486062 * 2
def baseEnd_486062 : Nat := 6162553923105741083695

theorem tailTrace_486062 : CollatzResearch.WordTrace tailWord_486062 prefixEnd_486062 6162553923105741083695 := by
  unfold tailWord_486062
  simp only [CollatzResearch.WordTrace]
  refine ⟨2216017195635982703215555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11818758376725241083816293 2216017195635982703215555)
  ·
    refine ⟨3324025793453974054823333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2216017195635982703215555 3324025793453974054823333)
    ·
      refine ⟨623254836272620135279375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3324025793453974054823333 623254836272620135279375)
      ·
        refine ⟨934882254408930202919063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 623254836272620135279375 934882254408930202919063)
        ·
          refine ⟨1402323381613395304378595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 934882254408930202919063 1402323381613395304378595)
          ·
            refine ⟨2103485072420092956567893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1402323381613395304378595 2103485072420092956567893)
            ·
              refine ⟨6162553923105741083695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2103485072420092956567893 6162553923105741083695)
              ·
                rfl

theorem cell22_486062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 10].length) (baseStart_486062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_486062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_486062 prefixEnd_486062 := by exact prefixLift 486062
  have htrace : WordTrace (prefixWord ++ tailWord_486062) baseStart_486062 baseEnd_486062 := by
    simpa [prefixWord, tailWord_486062, baseEnd_486062] using wordTrace_append hprefix tailTrace_486062
  have hstable : (prefixWord ++ tailWord_486062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486062).length < 2 ^ (prefixWord ++ tailWord_486062).sum := by decide
  have hdescent : baseEnd_486062 < baseStart_486062 := by decide
  rcases family_descends (prefixWord ++ tailWord_486062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486135 : List Nat := [1, 1, 3, 1, 1, 1, 3, 5, 6]
def baseStart_486135 : Nat := 118140960795 + 486135 * 2 ^ 59
def prefixEnd_486135 : Nat := 4983230072969 + 3 ^ 40 * 486135 * 2
def baseEnd_486135 : Nat := 55471315105235717394847

theorem tailTrace_486135 : CollatzResearch.WordTrace tailWord_486135 prefixEnd_486135 55471315105235717394847 := by
  unfold tailWord_486135
  simp only [CollatzResearch.WordTrace]
  refine ⟨17730800093823395093131859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11820533395882263395421239 17730800093823395093131859)
  ·
    refine ⟨26596200140735092639697789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17730800093823395093131859 26596200140735092639697789)
    ·
      refine ⟨9973575052775659739886671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26596200140735092639697789 9973575052775659739886671)
      ·
        refine ⟨14960362579163489609830007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9973575052775659739886671 14960362579163489609830007)
        ·
          refine ⟨22440543868745234414745011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14960362579163489609830007 22440543868745234414745011)
          ·
            refine ⟨33660815803117851622117517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22440543868745234414745011 33660815803117851622117517)
            ·
              refine ⟨12622805926169194358294069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33660815803117851622117517 12622805926169194358294069)
              ·
                refine ⟨1183388055578361971090069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12622805926169194358294069 1183388055578361971090069)
                ·
                  refine ⟨55471315105235717394847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1183388055578361971090069 55471315105235717394847)
                  ·
                    rfl

theorem cell22_486135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 5, 6].length) (baseStart_486135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_486135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_486135 prefixEnd_486135 := by exact prefixLift 486135
  have htrace : WordTrace (prefixWord ++ tailWord_486135) baseStart_486135 baseEnd_486135 := by
    simpa [prefixWord, tailWord_486135, baseEnd_486135] using wordTrace_append hprefix tailTrace_486135
  have hstable : (prefixWord ++ tailWord_486135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486135).length < 2 ^ (prefixWord ++ tailWord_486135).sum := by decide
  have hdescent : baseEnd_486135 < baseStart_486135 := by decide
  rcases family_descends (prefixWord ++ tailWord_486135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486152 : List Nat := [2, 1, 3, 2, 2, 3, 1, 2, 6]
def baseStart_486152 : Nat := 118140960795 + 486152 * 2 ^ 59
def prefixEnd_486152 : Nat := 4983230072969 + 3 ^ 40 * 486152 * 2
def baseEnd_486152 : Nat := 55473254921041591503163

theorem tailTrace_486152 : CollatzResearch.WordTrace tailWord_486152 prefixEnd_486152 55473254921041591503163 := by
  unfold tailWord_486152
  simp only [CollatzResearch.WordTrace]
  refine ⟨8865710067380903498250355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11820946756507871331000473 8865710067380903498250355)
  ·
    refine ⟨13298565101071355247375533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8865710067380903498250355 13298565101071355247375533)
    ·
      refine ⟨4986961912901758217765825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13298565101071355247375533 4986961912901758217765825)
      ·
        refine ⟨3740221434676318663324369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4986961912901758217765825 3740221434676318663324369)
        ·
          refine ⟨2805166076007238997493277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3740221434676318663324369 2805166076007238997493277)
          ·
            refine ⟨1051937278502714624059979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2805166076007238997493277 1051937278502714624059979)
            ·
              refine ⟨1577905917754071936089969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1051937278502714624059979 1577905917754071936089969)
              ·
                refine ⟨1183429438315553952067477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1577905917754071936089969 1183429438315553952067477)
                ·
                  refine ⟨55473254921041591503163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1183429438315553952067477 55473254921041591503163)
                  ·
                    rfl

theorem cell22_486152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 2, 6].length) (baseStart_486152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_486152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_486152 prefixEnd_486152 := by exact prefixLift 486152
  have htrace : WordTrace (prefixWord ++ tailWord_486152) baseStart_486152 baseEnd_486152 := by
    simpa [prefixWord, tailWord_486152, baseEnd_486152] using wordTrace_append hprefix tailTrace_486152
  have hstable : (prefixWord ++ tailWord_486152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486152).length < 2 ^ (prefixWord ++ tailWord_486152).sum := by decide
  have hdescent : baseEnd_486152 < baseStart_486152 := by decide
  rcases family_descends (prefixWord ++ tailWord_486152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486184 : List Nat := [2, 1, 5, 1, 1, 1, 3, 1, 4, 3]
def baseStart_486184 : Nat := 118140960795 + 486184 * 2 ^ 59
def prefixEnd_486184 : Nat := 4983230072969 + 3 ^ 40 * 486184 * 2
def baseEnd_486184 : Nat := 166430719017087357709391

theorem tailTrace_486184 : CollatzResearch.WordTrace tailWord_486184 prefixEnd_486184 166430719017087357709391 := by
  unfold tailWord_486184
  simp only [CollatzResearch.WordTrace]
  refine ⟨8866293635322938230832803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11821724847097250974443737 8866293635322938230832803)
  ·
    refine ⟨13299440452984407346249205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8866293635322938230832803 13299440452984407346249205)
    ·
      refine ⟨1246822542467288188710863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13299440452984407346249205 1246822542467288188710863)
      ·
        refine ⟨1870233813700932283066295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1246822542467288188710863 1870233813700932283066295)
        ·
          refine ⟨2805350720551398424599443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1870233813700932283066295 2805350720551398424599443)
          ·
            refine ⟨4208026080827097636899165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2805350720551398424599443 4208026080827097636899165)
            ·
              refine ⟨1578009780310161613837187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4208026080827097636899165 1578009780310161613837187)
              ·
                refine ⟨2367014670465242420755781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1578009780310161613837187 2367014670465242420755781)
                ·
                  refine ⟨443815250712232953891709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2367014670465242420755781 443815250712232953891709)
                  ·
                    refine ⟨166430719017087357709391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 443815250712232953891709 166430719017087357709391)
                    ·
                      rfl

theorem cell22_486184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_486184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_486184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_486184 prefixEnd_486184 := by exact prefixLift 486184
  have htrace : WordTrace (prefixWord ++ tailWord_486184) baseStart_486184 baseEnd_486184 := by
    simpa [prefixWord, tailWord_486184, baseEnd_486184] using wordTrace_append hprefix tailTrace_486184
  have hstable : (prefixWord ++ tailWord_486184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486184).length < 2 ^ (prefixWord ++ tailWord_486184).sum := by decide
  have hdescent : baseEnd_486184 < baseStart_486184 := by decide
  rcases family_descends (prefixWord ++ tailWord_486184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486186 : List Nat := [3, 1, 4, 3, 1, 1, 2, 1, 6]
def baseStart_486186 : Nat := 118140960795 + 486186 * 2 ^ 59
def prefixEnd_486186 : Nat := 4983230072969 + 3 ^ 40 * 486186 * 2
def baseEnd_486186 : Nat := 55477134552653339719795

theorem tailTrace_486186 : CollatzResearch.WordTrace tailWord_486186 prefixEnd_486186 55477134552653339719795 := by
  unfold tailWord_486186
  simp only [CollatzResearch.WordTrace]
  refine ⟨4433165054159657700809603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11821773477759087202158941 4433165054159657700809603)
  ·
    refine ⟨6649747581239486551214405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4433165054159657700809603 6649747581239486551214405)
    ·
      refine ⟨1246827671482403728352701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6649747581239486551214405 1246827671482403728352701)
      ·
        refine ⟨467560376805901398132263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1246827671482403728352701 467560376805901398132263)
        ·
          refine ⟨701340565208852097198395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467560376805901398132263 701340565208852097198395)
          ·
            refine ⟨1052010847813278145797593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 701340565208852097198395 1052010847813278145797593)
            ·
              refine ⟨789008135859958609348195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1052010847813278145797593 789008135859958609348195)
              ·
                refine ⟨1183512203789937914022293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 789008135859958609348195 1183512203789937914022293)
                ·
                  refine ⟨55477134552653339719795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1183512203789937914022293 55477134552653339719795)
                  ·
                    rfl

theorem cell22_486186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 1, 6].length) (baseStart_486186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_486186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_486186 prefixEnd_486186 := by exact prefixLift 486186
  have htrace : WordTrace (prefixWord ++ tailWord_486186) baseStart_486186 baseEnd_486186 := by
    simpa [prefixWord, tailWord_486186, baseEnd_486186] using wordTrace_append hprefix tailTrace_486186
  have hstable : (prefixWord ++ tailWord_486186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486186).length < 2 ^ (prefixWord ++ tailWord_486186).sum := by decide
  have hdescent : baseEnd_486186 < baseStart_486186 := by decide
  rcases family_descends (prefixWord ++ tailWord_486186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486259 : List Nat := [1, 1, 1, 2, 2, 1, 8, 1, 5]
def baseStart_486259 : Nat := 118140960795 + 486259 * 2 ^ 59
def prefixEnd_486259 : Nat := 4983230072969 + 3 ^ 40 * 486259 * 2
def baseEnd_486259 : Nat := 55485464349937387361387

theorem tailTrace_486259 : CollatzResearch.WordTrace tailWord_486259 prefixEnd_486259 55485464349937387361387 := by
  unfold tailWord_486259
  simp only [CollatzResearch.WordTrace]
  refine ⟨17735322745374164270645831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11823548496916109513763887 17735322745374164270645831)
  ·
    refine ⟨26602984118061246405968747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17735322745374164270645831 26602984118061246405968747)
    ·
      refine ⟨39904476177091869608953121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26602984118061246405968747 39904476177091869608953121)
      ·
        refine ⟨29928357132818902206714841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39904476177091869608953121 29928357132818902206714841)
        ·
          refine ⟨22446267849614176655036131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29928357132818902206714841 22446267849614176655036131)
          ·
            refine ⟨33669401774421264982554197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22446267849614176655036131 33669401774421264982554197)
            ·
              refine ⟨394563302043999199014307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 33669401774421264982554197 394563302043999199014307)
              ·
                refine ⟨591844953065998798521461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 394563302043999199014307 591844953065998798521461)
                ·
                  refine ⟨55485464349937387361387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 591844953065998798521461 55485464349937387361387)
                  ·
                    rfl

theorem cell22_486259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8, 1, 5].length) (baseStart_486259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_486259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_486259 prefixEnd_486259 := by exact prefixLift 486259
  have htrace : WordTrace (prefixWord ++ tailWord_486259) baseStart_486259 baseEnd_486259 := by
    simpa [prefixWord, tailWord_486259, baseEnd_486259] using wordTrace_append hprefix tailTrace_486259
  have hstable : (prefixWord ++ tailWord_486259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486259).length < 2 ^ (prefixWord ++ tailWord_486259).sum := by decide
  have hdescent : baseEnd_486259 < baseStart_486259 := by decide
  rcases family_descends (prefixWord ++ tailWord_486259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486334 : List Nat := [4, 2, 1, 1, 1, 2, 3, 1, 1, 6]
def baseStart_486334 : Nat := 118140960795 + 486334 * 2 ^ 59
def prefixEnd_486334 : Nat := 4983230072969 + 3 ^ 40 * 486334 * 2
def baseEnd_486334 : Nat := 166482067082536966458931

theorem tailTrace_486334 : CollatzResearch.WordTrace tailWord_486334 prefixEnd_486334 166482067082536966458931 := by
  unfold tailWord_486334
  simp only [CollatzResearch.WordTrace]
  refine ⟨2217257277512806509953257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11825372146734968053084037 2217257277512806509953257)
  ·
    refine ⟨1662942958134604882464943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2217257277512806509953257 1662942958134604882464943)
    ·
      refine ⟨2494414437201907323697415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1662942958134604882464943 2494414437201907323697415)
      ·
        refine ⟨3741621655802860985546123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2494414437201907323697415 3741621655802860985546123)
        ·
          refine ⟨5612432483704291478319185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3741621655802860985546123 5612432483704291478319185)
          ·
            refine ⟨4209324362778218608739389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5612432483704291478319185 4209324362778218608739389)
            ·
              refine ⟨1578496636041831978277271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4209324362778218608739389 1578496636041831978277271)
              ·
                refine ⟨2367744954062747967415907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1578496636041831978277271 2367744954062747967415907)
                ·
                  refine ⟨3551617431094121951123861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2367744954062747967415907 3551617431094121951123861)
                  ·
                    refine ⟨166482067082536966458931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3551617431094121951123861 166482067082536966458931)
                    ·
                      rfl

theorem cell22_486334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_486334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_486334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_486334 prefixEnd_486334 := by exact prefixLift 486334
  have htrace : WordTrace (prefixWord ++ tailWord_486334) baseStart_486334 baseEnd_486334 := by
    simpa [prefixWord, tailWord_486334, baseEnd_486334] using wordTrace_append hprefix tailTrace_486334
  have hstable : (prefixWord ++ tailWord_486334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486334).length < 2 ^ (prefixWord ++ tailWord_486334).sum := by decide
  have hdescent : baseEnd_486334 < baseStart_486334 := by decide
  rcases family_descends (prefixWord ++ tailWord_486334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486501 : List Nat := [1, 3, 1, 3, 2, 1, 5, 6]
def baseStart_486501 : Nat := 118140960795 + 486501 * 2 ^ 59
def prefixEnd_486501 : Nat := 4983230072969 + 3 ^ 40 * 486501 * 2
def baseEnd_486501 : Nat := 18504359399489355281491

theorem tailTrace_486501 : CollatzResearch.WordTrace tailWord_486501 prefixEnd_486501 18504359399489355281491 := by
  unfold tailWord_486501
  simp only [CollatzResearch.WordTrace]
  refine ⟨17744149210497439600955357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11829432806998293067303571 17744149210497439600955357)
  ·
    refine ⟨6654055953936539850358259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17744149210497439600955357 6654055953936539850358259)
    ·
      refine ⟨9981083930904809775537389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6654055953936539850358259 9981083930904809775537389)
      ·
        refine ⟨3742906474089303665826521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9981083930904809775537389 3742906474089303665826521)
        ·
          refine ⟨2807179855566977749369891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3742906474089303665826521 2807179855566977749369891)
          ·
            refine ⟨4210769783350466624054837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2807179855566977749369891 4210769783350466624054837)
            ·
              refine ⟨394759667189106246005141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4210769783350466624054837 394759667189106246005141)
              ·
                refine ⟨18504359399489355281491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 394759667189106246005141 18504359399489355281491)
                ·
                  rfl

theorem cell22_486501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 5, 6].length) (baseStart_486501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_486501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_486501 prefixEnd_486501 := by exact prefixLift 486501
  have htrace : WordTrace (prefixWord ++ tailWord_486501) baseStart_486501 baseEnd_486501 := by
    simpa [prefixWord, tailWord_486501, baseEnd_486501] using wordTrace_append hprefix tailTrace_486501
  have hstable : (prefixWord ++ tailWord_486501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486501).length < 2 ^ (prefixWord ++ tailWord_486501).sum := by decide
  have hdescent : baseEnd_486501 < baseStart_486501 := by decide
  rcases family_descends (prefixWord ++ tailWord_486501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486503 : List Nat := [1, 1, 5, 1, 1, 5, 1, 1, 2, 4]
def baseStart_486503 : Nat := 118140960795 + 486503 * 2 ^ 59
def prefixEnd_486503 : Nat := 4983230072969 + 3 ^ 40 * 486503 * 2
def baseEnd_486503 : Nat := 166539919236276858983413

theorem tailTrace_486503 : CollatzResearch.WordTrace tailWord_486503 prefixEnd_486503 166539919236276858983413 := by
  unfold tailWord_486503
  simp only [CollatzResearch.WordTrace]
  refine ⟨17744222156490193942528163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11829481437660129295018775 17744222156490193942528163)
  ·
    refine ⟨26616333234735290913792245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17744222156490193942528163 26616333234735290913792245)
    ·
      refine ⟨2495281240756433523168023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26616333234735290913792245 2495281240756433523168023)
      ·
        refine ⟨3742921861134650284752035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2495281240756433523168023 3742921861134650284752035)
        ·
          refine ⟨5614382791701975427128053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3742921861134650284752035 5614382791701975427128053)
          ·
            refine ⟨526348386722060196293255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5614382791701975427128053 526348386722060196293255)
            ·
              refine ⟨789522580083090294439883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 526348386722060196293255 789522580083090294439883)
              ·
                refine ⟨1184283870124635441659825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 789522580083090294439883 1184283870124635441659825)
                ·
                  refine ⟨888212902593476581244869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1184283870124635441659825 888212902593476581244869)
                  ·
                    refine ⟨166539919236276858983413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 888212902593476581244869 166539919236276858983413)
                    ·
                      rfl

theorem cell22_486503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_486503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_486503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_486503 prefixEnd_486503 := by exact prefixLift 486503
  have htrace : WordTrace (prefixWord ++ tailWord_486503) baseStart_486503 baseEnd_486503 := by
    simpa [prefixWord, tailWord_486503, baseEnd_486503] using wordTrace_append hprefix tailTrace_486503
  have hstable : (prefixWord ++ tailWord_486503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486503).length < 2 ^ (prefixWord ++ tailWord_486503).sum := by decide
  have hdescent : baseEnd_486503 < baseStart_486503 := by decide
  rcases family_descends (prefixWord ++ tailWord_486503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486544 : List Nat := [2, 1, 1, 1, 1, 1, 4, 3, 1, 7]
def baseStart_486544 : Nat := 118140960795 + 486544 * 2 ^ 59
def prefixEnd_486544 : Nat := 4983230072969 + 3 ^ 40 * 486544 * 2
def baseEnd_486544 : Nat := 166553954374166418708287

theorem tailTrace_486544 : CollatzResearch.WordTrace tailWord_486544 prefixEnd_486544 166553954374166418708287 := by
  unfold tailWord_486544
  simp only [CollatzResearch.WordTrace]
  refine ⟨8872858774670828972385343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11830478366227771963180457 8872858774670828972385343)
  ·
    refine ⟨13309288162006243458578015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8872858774670828972385343 13309288162006243458578015)
    ·
      refine ⟨19963932243009365187867023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13309288162006243458578015 19963932243009365187867023)
      ·
        refine ⟨29945898364514047781800535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19963932243009365187867023 29945898364514047781800535)
        ·
          refine ⟨44918847546771071672700803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29945898364514047781800535 44918847546771071672700803)
          ·
            refine ⟨67378271320156607509051205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44918847546771071672700803 67378271320156607509051205)
            ·
              refine ⟨12633425872529363907947101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67378271320156607509051205 12633425872529363907947101)
              ·
                refine ⟨4737534702198511465480163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12633425872529363907947101 4737534702198511465480163)
                ·
                  refine ⟨7106302053297767198220245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4737534702198511465480163 7106302053297767198220245)
                  ·
                    refine ⟨166553954374166418708287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7106302053297767198220245 166553954374166418708287)
                    ·
                      rfl

theorem cell22_486544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 1, 7].length) (baseStart_486544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_486544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_486544 prefixEnd_486544 := by exact prefixLift 486544
  have htrace : WordTrace (prefixWord ++ tailWord_486544) baseStart_486544 baseEnd_486544 := by
    simpa [prefixWord, tailWord_486544, baseEnd_486544] using wordTrace_append hprefix tailTrace_486544
  have hstable : (prefixWord ++ tailWord_486544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486544).length < 2 ^ (prefixWord ++ tailWord_486544).sum := by decide
  have hdescent : baseEnd_486544 < baseStart_486544 := by decide
  rcases family_descends (prefixWord ++ tailWord_486544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486567 : List Nat := [1, 1, 6, 2, 1, 1, 3, 3, 1, 3]
def baseStart_486567 : Nat := 118140960795 + 486567 * 2 ^ 59
def prefixEnd_486567 : Nat := 4983230072969 + 3 ^ 40 * 486567 * 2
def baseEnd_486567 : Nat := 166561827744202025383217

theorem tailTrace_486567 : CollatzResearch.WordTrace tailWord_486567 prefixEnd_486567 166561827744202025383217 := by
  unfold tailWord_486567
  simp only [CollatzResearch.WordTrace]
  refine ⟨17746556428258332872857955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11831037618838888581905303 17746556428258332872857955)
  ·
    refine ⟨26619834642387499309286933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17746556428258332872857955 26619834642387499309286933)
    ·
      refine ⟨1247804748861914030122825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 26619834642387499309286933 1247804748861914030122825)
      ·
        refine ⟨935853561646435522592119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1247804748861914030122825 935853561646435522592119)
        ·
          refine ⟨1403780342469653283888179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 935853561646435522592119 1403780342469653283888179)
          ·
            refine ⟨2105670513704479925832269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1403780342469653283888179 2105670513704479925832269)
            ·
              refine ⟨789626442639179972187101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2105670513704479925832269 789626442639179972187101)
              ·
                refine ⟨296109915989692489570163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 789626442639179972187101 296109915989692489570163)
                ·
                  refine ⟨444164873984538734355245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 296109915989692489570163 444164873984538734355245)
                  ·
                    refine ⟨166561827744202025383217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 444164873984538734355245 166561827744202025383217)
                    ·
                      rfl

theorem cell22_486567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_486567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_486567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_486567 prefixEnd_486567 := by exact prefixLift 486567
  have htrace : WordTrace (prefixWord ++ tailWord_486567) baseStart_486567 baseEnd_486567 := by
    simpa [prefixWord, tailWord_486567, baseEnd_486567] using wordTrace_append hprefix tailTrace_486567
  have hstable : (prefixWord ++ tailWord_486567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486567).length < 2 ^ (prefixWord ++ tailWord_486567).sum := by decide
  have hdescent : baseEnd_486567 < baseStart_486567 := by decide
  rcases family_descends (prefixWord ++ tailWord_486567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486591 : List Nat := [1, 1, 2, 2, 2, 2, 5, 1, 6]
def baseStart_486591 : Nat := 118140960795 + 486591 * 2 ^ 59
def prefixEnd_486591 : Nat := 4983230072969 + 3 ^ 40 * 486591 * 2
def baseEnd_486591 : Nat := 55523347811557987594381

theorem tailTrace_486591 : CollatzResearch.WordTrace tailWord_486591 prefixEnd_486591 55523347811557987594381 := by
  unfold tailWord_486591
  simp only [CollatzResearch.WordTrace]
  refine ⟨17747431780171384971731627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11831621186780923314487751 17747431780171384971731627)
  ·
    refine ⟨26621147670257077457597441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17747431780171384971731627 26621147670257077457597441)
    ·
      refine ⟨19965860752692808093198081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26621147670257077457597441 19965860752692808093198081)
      ·
        refine ⟨14974395564519606069898561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19965860752692808093198081 14974395564519606069898561)
        ·
          refine ⟨11230796673389704552423921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14974395564519606069898561 11230796673389704552423921)
          ·
            refine ⟨8423097505042278414317941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11230796673389704552423921 8423097505042278414317941)
            ·
              refine ⟨789665391097713601342307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8423097505042278414317941 789665391097713601342307)
              ·
                refine ⟨1184498086646570402013461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 789665391097713601342307 1184498086646570402013461)
                ·
                  refine ⟨55523347811557987594381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1184498086646570402013461 55523347811557987594381)
                  ·
                    rfl

theorem cell22_486591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 1, 6].length) (baseStart_486591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_486591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_486591 prefixEnd_486591 := by exact prefixLift 486591
  have htrace : WordTrace (prefixWord ++ tailWord_486591) baseStart_486591 baseEnd_486591 := by
    simpa [prefixWord, tailWord_486591, baseEnd_486591] using wordTrace_append hprefix tailTrace_486591
  have hstable : (prefixWord ++ tailWord_486591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486591).length < 2 ^ (prefixWord ++ tailWord_486591).sum := by decide
  have hdescent : baseEnd_486591 < baseStart_486591 := by decide
  rcases family_descends (prefixWord ++ tailWord_486591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486638 : List Nat := [4, 1, 2, 1, 1, 1, 4, 2, 2, 4]
def baseStart_486638 : Nat := 118140960795 + 486638 * 2 ^ 59
def prefixEnd_486638 : Nat := 4983230072969 + 3 ^ 40 * 486638 * 2
def baseEnd_486638 : Nat := 166586132495181506857999

theorem tailTrace_486638 : CollatzResearch.WordTrace tailWord_486638 prefixEnd_486638 166586132495181506857999 := by
  unfold tailWord_486638
  simp only [CollatzResearch.WordTrace]
  refine ⟨2218643251375138999836571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11832764007334074665795045 2218643251375138999836571)
  ·
    refine ⟨3327964877062708499754857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2218643251375138999836571 3327964877062708499754857)
    ·
      refine ⟨2495973657797031374816143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3327964877062708499754857 2495973657797031374816143)
      ·
        refine ⟨3743960486695547062224215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2495973657797031374816143 3743960486695547062224215)
        ·
          refine ⟨5615940730043320593336323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3743960486695547062224215 5615940730043320593336323)
          ·
            refine ⟨8423911095064980890004485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5615940730043320593336323 8423911095064980890004485)
            ·
              refine ⟨1579483330324683916875841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8423911095064980890004485 1579483330324683916875841)
              ·
                refine ⟨1184612497743512937656881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1579483330324683916875841 1184612497743512937656881)
                ·
                  refine ⟨888459373307634703242661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1184612497743512937656881 888459373307634703242661)
                  ·
                    refine ⟨166586132495181506857999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 888459373307634703242661 166586132495181506857999)
                    ·
                      rfl

theorem cell22_486638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_486638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_486638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_486638 prefixEnd_486638 := by exact prefixLift 486638
  have htrace : WordTrace (prefixWord ++ tailWord_486638) baseStart_486638 baseEnd_486638 := by
    simpa [prefixWord, tailWord_486638, baseEnd_486638] using wordTrace_append hprefix tailTrace_486638
  have hstable : (prefixWord ++ tailWord_486638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486638).length < 2 ^ (prefixWord ++ tailWord_486638).sum := by decide
  have hdescent : baseEnd_486638 < baseStart_486638 := by decide
  rcases family_descends (prefixWord ++ tailWord_486638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486666 : List Nat := [3, 1, 2, 2, 1, 1, 1, 1, 4, 6]
def baseStart_486666 : Nat := 118140960795 + 486666 * 2 ^ 59
def prefixEnd_486666 : Nat := 4983230072969 + 3 ^ 40 * 486666 * 2
def baseEnd_486666 : Nat := 166595717467398767157913

theorem tailTrace_486666 : CollatzResearch.WordTrace tailWord_486666 prefixEnd_486666 166595717467398767157913 := by
  unfold tailWord_486666
  simp only [CollatzResearch.WordTrace]
  refine ⟨4437541813724918195177963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11833444836599781853807901 4437541813724918195177963)
  ·
    refine ⟨6656312720587377292766945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4437541813724918195177963 6656312720587377292766945)
    ·
      refine ⟨4992234540440532969575209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6656312720587377292766945 4992234540440532969575209)
      ·
        refine ⟨3744175905330399727181407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4992234540440532969575209 3744175905330399727181407)
        ·
          refine ⟨5616263857995599590772111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3744175905330399727181407 5616263857995599590772111)
          ·
            refine ⟨8424395786993399386158167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5616263857995599590772111 8424395786993399386158167)
            ·
              refine ⟨12636593680490099079237251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8424395786993399386158167 12636593680490099079237251)
              ·
                refine ⟨18954890520735148618855877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12636593680490099079237251 18954890520735148618855877)
                ·
                  refine ⟨3554041972637840366035477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18954890520735148618855877 3554041972637840366035477)
                  ·
                    refine ⟨166595717467398767157913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3554041972637840366035477 166595717467398767157913)
                    ·
                      rfl

theorem cell22_486666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_486666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_486666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_486666 prefixEnd_486666 := by exact prefixLift 486666
  have htrace : WordTrace (prefixWord ++ tailWord_486666) baseStart_486666 baseEnd_486666 := by
    simpa [prefixWord, tailWord_486666, baseEnd_486666] using wordTrace_append hprefix tailTrace_486666
  have hstable : (prefixWord ++ tailWord_486666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486666).length < 2 ^ (prefixWord ++ tailWord_486666).sum := by decide
  have hdescent : baseEnd_486666 < baseStart_486666 := by decide
  rcases family_descends (prefixWord ++ tailWord_486666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486668 : List Nat := [2, 2, 1, 2, 2, 3, 1, 1, 5, 3]
def baseStart_486668 : Nat := 118140960795 + 486668 * 2 ^ 59
def prefixEnd_486668 : Nat := 4983230072969 + 3 ^ 40 * 486668 * 2
def baseEnd_486668 : Nat := 166596402108271428607907

theorem tailTrace_486668 : CollatzResearch.WordTrace tailWord_486668 prefixEnd_486668 166596402108271428607907 := by
  unfold tailWord_486668
  simp only [CollatzResearch.WordTrace]
  refine ⟨8875120100446213561142329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11833493467261618081523105 8875120100446213561142329)
  ·
    refine ⟨6656340075334660170856747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8875120100446213561142329 6656340075334660170856747)
    ·
      refine ⟨9984510113001990256285121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6656340075334660170856747 9984510113001990256285121)
      ·
        refine ⟨7488382584751492692213841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9984510113001990256285121 7488382584751492692213841)
        ·
          refine ⟨5616286938563619519160381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7488382584751492692213841 5616286938563619519160381)
          ·
            refine ⟨2106107601961357319685143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5616286938563619519160381 2106107601961357319685143)
            ·
              refine ⟨3159161402942035979527715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2106107601961357319685143 3159161402942035979527715)
              ·
                refine ⟨4738742104413053969291573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3159161402942035979527715 4738742104413053969291573)
                ·
                  refine ⟨444257072288723809621085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4738742104413053969291573 444257072288723809621085)
                  ·
                    refine ⟨166596402108271428607907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 444257072288723809621085 166596402108271428607907)
                    ·
                      rfl

theorem cell22_486668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 5, 3].length) (baseStart_486668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_486668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_486668 prefixEnd_486668 := by exact prefixLift 486668
  have htrace : WordTrace (prefixWord ++ tailWord_486668) baseStart_486668 baseEnd_486668 := by
    simpa [prefixWord, tailWord_486668, baseEnd_486668] using wordTrace_append hprefix tailTrace_486668
  have hstable : (prefixWord ++ tailWord_486668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486668).length < 2 ^ (prefixWord ++ tailWord_486668).sum := by decide
  have hdescent : baseEnd_486668 < baseStart_486668 := by decide
  rcases family_descends (prefixWord ++ tailWord_486668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486766 : List Nat := [4, 1, 2, 4, 2, 1, 2, 1, 5]
def baseStart_486766 : Nat := 118140960795 + 486766 * 2 ^ 59
def prefixEnd_486766 : Nat := 4983230072969 + 3 ^ 40 * 486766 * 2
def baseEnd_486766 : Nat := 55543316503677279885869

theorem tailTrace_486766 : CollatzResearch.WordTrace tailWord_486766 prefixEnd_486766 55543316503677279885869 := by
  unfold tailWord_486766
  simp only [CollatzResearch.WordTrace]
  refine ⟨2219226819317173732419019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11835876369691593239568101 2219226819317173732419019)
  ·
    refine ⟨3328840228975760598628529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2219226819317173732419019 3328840228975760598628529)
    ·
      refine ⟨2496630171731820448971397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3328840228975760598628529 2496630171731820448971397)
      ·
        refine ⟨468118157199716334182137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2496630171731820448971397 468118157199716334182137)
        ·
          refine ⟨351088617899787250636603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 468118157199716334182137 351088617899787250636603)
          ·
            refine ⟨526632926849680875954905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351088617899787250636603 526632926849680875954905)
            ·
              refine ⟨394974695137260656966179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 526632926849680875954905 394974695137260656966179)
              ·
                refine ⟨592462042705890985449269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 394974695137260656966179 592462042705890985449269)
                ·
                  refine ⟨55543316503677279885869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 592462042705890985449269 55543316503677279885869)
                  ·
                    rfl

theorem cell22_486766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 2, 1, 5].length) (baseStart_486766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_486766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_486766 prefixEnd_486766 := by exact prefixLift 486766
  have htrace : WordTrace (prefixWord ++ tailWord_486766) baseStart_486766 baseEnd_486766 := by
    simpa [prefixWord, tailWord_486766, baseEnd_486766] using wordTrace_append hprefix tailTrace_486766
  have hstable : (prefixWord ++ tailWord_486766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486766).length < 2 ^ (prefixWord ++ tailWord_486766).sum := by decide
  have hdescent : baseEnd_486766 < baseStart_486766 := by decide
  rcases family_descends (prefixWord ++ tailWord_486766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486775 : List Nat := [1, 1, 3, 1, 1, 2, 5, 3, 2, 3]
def baseStart_486775 : Nat := 118140960795 + 486775 * 2 ^ 59
def prefixEnd_486775 : Nat := 4983230072969 + 3 ^ 40 * 486775 * 2
def baseEnd_486775 : Nat := 166633030394958816182579

theorem tailTrace_486775 : CollatzResearch.WordTrace tailWord_486775 prefixEnd_486775 166633030394958816182579 := by
  unfold tailWord_486775
  simp only [CollatzResearch.WordTrace]
  refine ⟨17754142811504784396429779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11836095207669856264286519 17754142811504784396429779)
  ·
    refine ⟨26631214217257176594644669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17754142811504784396429779 26631214217257176594644669)
    ·
      refine ⟨9986705331471441222991751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26631214217257176594644669 9986705331471441222991751)
      ·
        refine ⟨14980057997207161834487627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9986705331471441222991751 14980057997207161834487627)
        ·
          refine ⟨22470086995810742751731441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14980057997207161834487627 22470086995810742751731441)
          ·
            refine ⟨16852565246858057063798581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22470086995810742751731441 16852565246858057063798581)
            ·
              refine ⟨1579927991892942849731117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16852565246858057063798581 1579927991892942849731117)
              ·
                refine ⟨592472996959853568649169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1579927991892942849731117 592472996959853568649169)
                ·
                  refine ⟨444354747719890176486877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 592472996959853568649169 444354747719890176486877)
                  ·
                    refine ⟨166633030394958816182579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 444354747719890176486877 166633030394958816182579)
                    ·
                      rfl

theorem cell22_486775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 3, 2, 3].length) (baseStart_486775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_486775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_486775 prefixEnd_486775 := by exact prefixLift 486775
  have htrace : WordTrace (prefixWord ++ tailWord_486775) baseStart_486775 baseEnd_486775 := by
    simpa [prefixWord, tailWord_486775, baseEnd_486775] using wordTrace_append hprefix tailTrace_486775
  have hstable : (prefixWord ++ tailWord_486775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486775).length < 2 ^ (prefixWord ++ tailWord_486775).sum := by decide
  have hdescent : baseEnd_486775 < baseStart_486775 := by decide
  rcases family_descends (prefixWord ++ tailWord_486775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486788 : List Nat := [2, 3, 2, 1, 1, 3, 2, 8]
def baseStart_486788 : Nat := 118140960795 + 486788 * 2 ^ 59
def prefixEnd_486788 : Nat := 4983230072969 + 3 ^ 40 * 486788 * 2
def baseEnd_486788 : Nat := 18515275617847901734171

theorem tailTrace_486788 : CollatzResearch.WordTrace tailWord_486788 prefixEnd_486788 18515275617847901734171 := by
  unfold tailWord_486788
  simp only [CollatzResearch.WordTrace]
  refine ⟨8877308480228843808326509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11836411306971791744435345 8877308480228843808326509)
  ·
    refine ⟨3328990680085816428122441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8877308480228843808326509 3328990680085816428122441)
    ·
      refine ⟨2496743010064362321091831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3328990680085816428122441 2496743010064362321091831)
      ·
        refine ⟨3745114515096543481637747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2496743010064362321091831 3745114515096543481637747)
        ·
          refine ⟨5617671772644815222456621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3745114515096543481637747 5617671772644815222456621)
          ·
            refine ⟨2106626914741805708421233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5617671772644815222456621 2106626914741805708421233)
            ·
              refine ⟨1579970186056354281315925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2106626914741805708421233 1579970186056354281315925)
              ·
                refine ⟨18515275617847901734171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1579970186056354281315925 18515275617847901734171)
                ·
                  rfl

theorem cell22_486788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 8].length) (baseStart_486788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_486788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_486788 prefixEnd_486788 := by exact prefixLift 486788
  have htrace : WordTrace (prefixWord ++ tailWord_486788) baseStart_486788 baseEnd_486788 := by
    simpa [prefixWord, tailWord_486788, baseEnd_486788] using wordTrace_append hprefix tailTrace_486788
  have hstable : (prefixWord ++ tailWord_486788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486788).length < 2 ^ (prefixWord ++ tailWord_486788).sum := by decide
  have hdescent : baseEnd_486788 < baseStart_486788 := by decide
  rcases family_descends (prefixWord ++ tailWord_486788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486820 : List Nat := [2, 3, 1, 2, 1, 1, 1, 5, 3, 3]
def baseStart_486820 : Nat := 118140960795 + 486820 * 2 ^ 59
def prefixEnd_486820 : Nat := 4983230072969 + 3 ^ 40 * 486820 * 2
def baseEnd_486820 : Nat := 166648434814593698807441

theorem tailTrace_486820 : CollatzResearch.WordTrace tailWord_486820 prefixEnd_486820 166648434814593698807441 := by
  unfold tailWord_486820
  simp only [CollatzResearch.WordTrace]
  refine ⟨8877892048170878540908957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11837189397561171387878609 8877892048170878540908957)
  ·
    refine ⟨3329209518064079452840859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8877892048170878540908957 3329209518064079452840859)
    ·
      refine ⟨4993814277096119179261289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3329209518064079452840859 4993814277096119179261289)
      ·
        refine ⟨3745360707822089384445967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4993814277096119179261289 3745360707822089384445967)
        ·
          refine ⟨5618041061733134076668951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3745360707822089384445967 5618041061733134076668951)
          ·
            refine ⟨8427061592599701115003427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5618041061733134076668951 8427061592599701115003427)
            ·
              refine ⟨12640592388899551672505141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8427061592599701115003427 12640592388899551672505141)
              ·
                refine ⟨1185055536459332969297357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12640592388899551672505141 1185055536459332969297357)
                ·
                  refine ⟨444395826172249863486509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1185055536459332969297357 444395826172249863486509)
                  ·
                    refine ⟨166648434814593698807441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 444395826172249863486509 166648434814593698807441)
                    ·
                      rfl

theorem cell22_486820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 5, 3, 3].length) (baseStart_486820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_486820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_486820 prefixEnd_486820 := by exact prefixLift 486820
  have htrace : WordTrace (prefixWord ++ tailWord_486820) baseStart_486820 baseEnd_486820 := by
    simpa [prefixWord, tailWord_486820, baseEnd_486820] using wordTrace_append hprefix tailTrace_486820
  have hstable : (prefixWord ++ tailWord_486820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486820).length < 2 ^ (prefixWord ++ tailWord_486820).sum := by decide
  have hdescent : baseEnd_486820 < baseStart_486820 := by decide
  rcases family_descends (prefixWord ++ tailWord_486820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486837 : List Nat := [1, 3, 3, 2, 2, 2, 1, 2, 3, 3]
def baseStart_486837 : Nat := 118140960795 + 486837 * 2 ^ 59
def prefixEnd_486837 : Nat := 4983230072969 + 3 ^ 40 * 486837 * 2
def baseEnd_486837 : Nat := 166654254262011321132389

theorem tailTrace_486837 : CollatzResearch.WordTrace tailWord_486837 prefixEnd_486837 166654254262011321132389 := by
  unfold tailWord_486837
  simp only [CollatzResearch.WordTrace]
  refine ⟨17756404137280168985186765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11837602758186779323457843 17756404137280168985186765)
  ·
    refine ⟨6658651551480063369445037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17756404137280168985186765 6658651551480063369445037)
    ·
      refine ⟨2496994331805023763541889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6658651551480063369445037 2496994331805023763541889)
      ·
        refine ⟨1872745748853767822656417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2496994331805023763541889 1872745748853767822656417)
        ·
          refine ⟨1404559311640325866992313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1872745748853767822656417 1404559311640325866992313)
          ·
            refine ⟨1053419483730244400244235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1404559311640325866992313 1053419483730244400244235)
            ·
              refine ⟨1580129225595366600366353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1053419483730244400244235 1580129225595366600366353)
              ·
                refine ⟨1185096919196524950274765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1580129225595366600366353 1185096919196524950274765)
                ·
                  refine ⟨444411344698696856353037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1185096919196524950274765 444411344698696856353037)
                  ·
                    refine ⟨166654254262011321132389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 444411344698696856353037 166654254262011321132389)
                    ·
                      rfl

theorem cell22_486837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_486837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_486837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_486837 prefixEnd_486837 := by exact prefixLift 486837
  have htrace : WordTrace (prefixWord ++ tailWord_486837) baseStart_486837 baseEnd_486837 := by
    simpa [prefixWord, tailWord_486837, baseEnd_486837] using wordTrace_append hprefix tailTrace_486837
  have hstable : (prefixWord ++ tailWord_486837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486837).length < 2 ^ (prefixWord ++ tailWord_486837).sum := by decide
  have hdescent : baseEnd_486837 < baseStart_486837 := by decide
  rcases family_descends (prefixWord ++ tailWord_486837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486897 : List Nat := [1, 2, 2, 2, 3, 3, 2, 2, 1, 4]
def baseStart_486897 : Nat := 118140960795 + 486897 * 2 ^ 59
def prefixEnd_486897 : Nat := 4983230072969 + 3 ^ 40 * 486897 * 2
def baseEnd_486897 : Nat := 166674793488191164632205

theorem tailTrace_486897 : CollatzResearch.WordTrace tailWord_486897 prefixEnd_486897 166674793488191164632205 := by
  unfold tailWord_486897
  simp only [CollatzResearch.WordTrace]
  refine ⟨17758592517062799232370945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11839061678041866154913963 17758592517062799232370945)
  ·
    refine ⟨13318944387797099424278209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17758592517062799232370945 13318944387797099424278209)
    ·
      refine ⟨9989208290847824568208657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13318944387797099424278209 9989208290847824568208657)
      ·
        refine ⟨7491906218135868426156493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9989208290847824568208657 7491906218135868426156493)
        ·
          refine ⟨2809464831800950659808685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7491906218135868426156493 2809464831800950659808685)
          ·
            refine ⟨1053549311925356497428257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2809464831800950659808685 1053549311925356497428257)
            ·
              refine ⟨790161983944017373071193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1053549311925356497428257 790161983944017373071193)
              ·
                refine ⟨592621487958013029803395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 790161983944017373071193 592621487958013029803395)
                ·
                  refine ⟨888932231937019544705093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 592621487958013029803395 888932231937019544705093)
                  ·
                    refine ⟨166674793488191164632205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 888932231937019544705093 166674793488191164632205)
                    ·
                      rfl

theorem cell22_486897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 2, 1, 4].length) (baseStart_486897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_486897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_486897 prefixEnd_486897 := by exact prefixLift 486897
  have htrace : WordTrace (prefixWord ++ tailWord_486897) baseStart_486897 baseEnd_486897 := by
    simpa [prefixWord, tailWord_486897, baseEnd_486897] using wordTrace_append hprefix tailTrace_486897
  have hstable : (prefixWord ++ tailWord_486897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486897).length < 2 ^ (prefixWord ++ tailWord_486897).sum := by decide
  have hdescent : baseEnd_486897 < baseStart_486897 := by decide
  rcases family_descends (prefixWord ++ tailWord_486897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486914 : List Nat := [3, 4, 1, 2, 1, 1, 2, 3, 1, 4]
def baseStart_486914 : Nat := 118140960795 + 486914 * 2 ^ 59
def prefixEnd_486914 : Nat := 4983230072969 + 3 ^ 40 * 486914 * 2
def baseEnd_486914 : Nat := 166680612935608786957153

theorem tailTrace_486914 : CollatzResearch.WordTrace tailWord_486914 prefixEnd_486914 166680612935608786957153 := by
  unfold tailWord_486914
  simp only [CollatzResearch.WordTrace]
  refine ⟨4439803139500302783934949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11839475038667474090493197 4439803139500302783934949)
  ·
    refine ⟨832463088656306771987803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4439803139500302783934949 832463088656306771987803)
    ·
      refine ⟨1248694632984460157981705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 832463088656306771987803 1248694632984460157981705)
      ·
        refine ⟨936520974738345118486279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1248694632984460157981705 936520974738345118486279)
        ·
          refine ⟨1404781462107517677729419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 936520974738345118486279 1404781462107517677729419)
          ·
            refine ⟨2107172193161276516594129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1404781462107517677729419 2107172193161276516594129)
            ·
              refine ⟨1580379144870957387445597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2107172193161276516594129 1580379144870957387445597)
              ·
                refine ⟨592642179326609020292099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1580379144870957387445597 592642179326609020292099)
                ·
                  refine ⟨888963268989913530438149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 592642179326609020292099 888963268989913530438149)
                  ·
                    refine ⟨166680612935608786957153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 888963268989913530438149 166680612935608786957153)
                    ·
                      rfl

theorem cell22_486914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_486914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_486914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_486914 prefixEnd_486914 := by exact prefixLift 486914
  have htrace : WordTrace (prefixWord ++ tailWord_486914) baseStart_486914 baseEnd_486914 := by
    simpa [prefixWord, tailWord_486914, baseEnd_486914] using wordTrace_append hprefix tailTrace_486914
  have hstable : (prefixWord ++ tailWord_486914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486914).length < 2 ^ (prefixWord ++ tailWord_486914).sum := by decide
  have hdescent : baseEnd_486914 < baseStart_486914 := by decide
  rcases family_descends (prefixWord ++ tailWord_486914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486940 : List Nat := [2, 2, 3, 1, 2, 1, 4, 7]
def baseStart_486940 : Nat := 118140960795 + 486940 * 2 ^ 59
def prefixEnd_486940 : Nat := 4983230072969 + 3 ^ 40 * 486940 * 2
def baseEnd_486940 : Nat := 18521057029661487311897

theorem tailTrace_486940 : CollatzResearch.WordTrace tailWord_486940 prefixEnd_486940 18521057029661487311897 := by
  unfold tailWord_486940
  simp only [CollatzResearch.WordTrace]
  refine ⟨8880080427953508788093137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11840107237271345050790849 8880080427953508788093137)
  ·
    refine ⟨6660060320965131591069853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8880080427953508788093137 6660060320965131591069853)
    ·
      refine ⟨2497522620361924346651195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6660060320965131591069853 2497522620361924346651195)
      ·
        refine ⟨3746283930542886519976793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2497522620361924346651195 3746283930542886519976793)
        ·
          refine ⟨2809712947907164889982595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3746283930542886519976793 2809712947907164889982595)
          ·
            refine ⟨4214569421860747334973893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2809712947907164889982595 4214569421860747334973893)
            ·
              refine ⟨790231766598890125307605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4214569421860747334973893 790231766598890125307605)
              ·
                refine ⟨18521057029661487311897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 790231766598890125307605 18521057029661487311897)
                ·
                  rfl

theorem cell22_486940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 7].length) (baseStart_486940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_486940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_486940 prefixEnd_486940 := by exact prefixLift 486940
  have htrace : WordTrace (prefixWord ++ tailWord_486940) baseStart_486940 baseEnd_486940 := by
    simpa [prefixWord, tailWord_486940, baseEnd_486940] using wordTrace_append hprefix tailTrace_486940
  have hstable : (prefixWord ++ tailWord_486940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486940).length < 2 ^ (prefixWord ++ tailWord_486940).sum := by decide
  have hdescent : baseEnd_486940 < baseStart_486940 := by decide
  rcases family_descends (prefixWord ++ tailWord_486940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486944 : List Nat := [2, 1, 1, 6, 1, 2, 1, 3, 2, 3]
def baseStart_486944 : Nat := 118140960795 + 486944 * 2 ^ 59
def prefixEnd_486944 : Nat := 4983230072969 + 3 ^ 40 * 486944 * 2
def baseEnd_486944 : Nat := 166690882548698708707061

theorem tailTrace_486944 : CollatzResearch.WordTrace tailWord_486944 prefixEnd_486944 166690882548698708707061 := by
  unfold tailWord_486944
  simp only [CollatzResearch.WordTrace]
  refine ⟨8880153373946263129665943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11840204498595017506221257 8880153373946263129665943)
  ·
    refine ⟨13320230060919394694498915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8880153373946263129665943 13320230060919394694498915)
    ·
      refine ⟨19980345091379092041748373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13320230060919394694498915 19980345091379092041748373)
      ·
        refine ⟨936578676158394939456955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 19980345091379092041748373 936578676158394939456955)
        ·
          refine ⟨1404868014237592409185433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 936578676158394939456955 1404868014237592409185433)
          ·
            refine ⟨1053651010678194306889075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1404868014237592409185433 1053651010678194306889075)
            ·
              refine ⟨1580476516017291460333613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1053651010678194306889075 1580476516017291460333613)
              ·
                refine ⟨592678693506484297625105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1580476516017291460333613 592678693506484297625105)
                ·
                  refine ⟨444509020129863223218829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 592678693506484297625105 444509020129863223218829)
                  ·
                    refine ⟨166690882548698708707061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 444509020129863223218829 166690882548698708707061)
                    ·
                      rfl

theorem cell22_486944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 3, 2, 3].length) (baseStart_486944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_486944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_486944 prefixEnd_486944 := by exact prefixLift 486944
  have htrace : WordTrace (prefixWord ++ tailWord_486944) baseStart_486944 baseEnd_486944 := by
    simpa [prefixWord, tailWord_486944, baseEnd_486944] using wordTrace_append hprefix tailTrace_486944
  have hstable : (prefixWord ++ tailWord_486944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486944).length < 2 ^ (prefixWord ++ tailWord_486944).sum := by decide
  have hdescent : baseEnd_486944 < baseStart_486944 := by decide
  rcases family_descends (prefixWord ++ tailWord_486944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487047 : List Nat := [1, 1, 4, 2, 1, 4, 2, 1, 6]
def baseStart_487047 : Nat := 118140960795 + 487047 * 2 ^ 59
def prefixEnd_487047 : Nat := 4983230072969 + 3 ^ 40 * 487047 * 2
def baseEnd_487047 : Nat := 55575380517880257793915

theorem tailTrace_487047 : CollatzResearch.WordTrace tailWord_487047 prefixEnd_487047 55575380517880257793915 := by
  unfold tailWord_487047
  simp only [CollatzResearch.WordTrace]
  refine ⟨17764063466519374850331395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11842708977679583233554263 17764063466519374850331395)
  ·
    refine ⟨26646095199779062275497093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17764063466519374850331395 26646095199779062275497093)
    ·
      refine ⟨4996142849958574176655705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26646095199779062275497093 4996142849958574176655705)
      ·
        refine ⟨3747107137468930632491779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4996142849958574176655705 3747107137468930632491779)
        ·
          refine ⟨5620660706203395948737669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3747107137468930632491779 5620660706203395948737669)
          ·
            refine ⟨1053873882413136740388313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5620660706203395948737669 1053873882413136740388313)
            ·
              refine ⟨790405411809852555291235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1053873882413136740388313 790405411809852555291235)
              ·
                refine ⟨1185608117714778832936853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 790405411809852555291235 1185608117714778832936853)
                ·
                  refine ⟨55575380517880257793915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1185608117714778832936853 55575380517880257793915)
                  ·
                    rfl

theorem cell22_487047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 1, 6].length) (baseStart_487047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_487047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_487047 prefixEnd_487047 := by exact prefixLift 487047
  have htrace : WordTrace (prefixWord ++ tailWord_487047) baseStart_487047 baseEnd_487047 := by
    simpa [prefixWord, tailWord_487047, baseEnd_487047] using wordTrace_append hprefix tailTrace_487047
  have hstable : (prefixWord ++ tailWord_487047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487047).length < 2 ^ (prefixWord ++ tailWord_487047).sum := by decide
  have hdescent : baseEnd_487047 < baseStart_487047 := by decide
  rcases family_descends (prefixWord ++ tailWord_487047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487075 : List Nat := [1, 1, 1, 4, 1, 1, 5, 8]
def baseStart_487075 : Nat := 118140960795 + 487075 * 2 ^ 59
def prefixEnd_487075 : Nat := 4983230072969 + 3 ^ 40 * 487075 * 2
def baseEnd_487075 : Nat := 18526191836206448186851

theorem tailTrace_487075 : CollatzResearch.WordTrace tailWord_487075 prefixEnd_487075 18526191836206448186851 := by
  unfold tailWord_487075
  simp only [CollatzResearch.WordTrace]
  refine ⟨17765084710417935632350679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11843389806945290421567119 17765084710417935632350679)
  ·
    refine ⟨26647627065626903448526019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17765084710417935632350679 26647627065626903448526019)
    ·
      refine ⟨39971440598440355172789029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26647627065626903448526019 39971440598440355172789029)
      ·
        refine ⟨7494645112207566594897943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39971440598440355172789029 7494645112207566594897943)
        ·
          refine ⟨11241967668311349892346915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7494645112207566594897943 11241967668311349892346915)
          ·
            refine ⟨16862951502467024838520373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11241967668311349892346915 16862951502467024838520373)
            ·
              refine ⟨1580901703356283578611285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16862951502467024838520373 1580901703356283578611285)
              ·
                refine ⟨18526191836206448186851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1580901703356283578611285 18526191836206448186851)
                ·
                  rfl

theorem cell22_487075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 8].length) (baseStart_487075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_487075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_487075 prefixEnd_487075 := by exact prefixLift 487075
  have htrace : WordTrace (prefixWord ++ tailWord_487075) baseStart_487075 baseEnd_487075 := by
    simpa [prefixWord, tailWord_487075, baseEnd_487075] using wordTrace_append hprefix tailTrace_487075
  have hstable : (prefixWord ++ tailWord_487075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487075).length < 2 ^ (prefixWord ++ tailWord_487075).sum := by decide
  have hdescent : baseEnd_487075 < baseStart_487075 := by decide
  rcases family_descends (prefixWord ++ tailWord_487075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487120 : List Nat := [2, 1, 1, 1, 1, 2, 1, 4, 9]
def baseStart_487120 : Nat := 118140960795 + 487120 * 2 ^ 59
def prefixEnd_487120 : Nat := 4983230072969 + 3 ^ 40 * 487120 * 2
def baseEnd_487120 : Nat := 55583710315164305435507

theorem tailTrace_487120 : CollatzResearch.WordTrace tailWord_487120 prefixEnd_487120 55583710315164305435507 := by
  unfold tailWord_487120
  simp only [CollatzResearch.WordTrace]
  refine ⟨8883362997627454158869407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11844483996836605545159209 8883362997627454158869407)
  ·
    refine ⟨13325044496441181238304111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8883362997627454158869407 13325044496441181238304111)
    ·
      refine ⟨19987566744661771857456167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13325044496441181238304111 19987566744661771857456167)
      ·
        refine ⟨29981350116992657786184251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19987566744661771857456167 29981350116992657786184251)
        ·
          refine ⟨44972025175488986679276377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29981350116992657786184251 44972025175488986679276377)
          ·
            refine ⟨33729018881616740009457283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44972025175488986679276377 33729018881616740009457283)
            ·
              refine ⟨50593528322425110014185925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33729018881616740009457283 50593528322425110014185925)
              ·
                refine ⟨9486286560454708127659861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50593528322425110014185925 9486286560454708127659861)
                ·
                  refine ⟨55583710315164305435507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 9486286560454708127659861 55583710315164305435507)
                  ·
                    rfl

theorem cell22_487120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 9].length) (baseStart_487120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_487120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_487120 prefixEnd_487120 := by exact prefixLift 487120
  have htrace : WordTrace (prefixWord ++ tailWord_487120) baseStart_487120 baseEnd_487120 := by
    simpa [prefixWord, tailWord_487120, baseEnd_487120] using wordTrace_append hprefix tailTrace_487120
  have hstable : (prefixWord ++ tailWord_487120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487120).length < 2 ^ (prefixWord ++ tailWord_487120).sum := by decide
  have hdescent : baseEnd_487120 < baseStart_487120 := by decide
  rcases family_descends (prefixWord ++ tailWord_487120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487141 : List Nat := [1, 3, 1, 4, 1, 1, 2, 5, 1, 3]
def baseStart_487141 : Nat := 118140960795 + 487141 * 2 ^ 59
def prefixEnd_487141 : Nat := 4983230072969 + 3 ^ 40 * 487141 * 2
def baseEnd_487141 : Nat := 166758319674655861531457

theorem tailTrace_487141 : CollatzResearch.WordTrace tailWord_487141 prefixEnd_487141 166758319674655861531457 := by
  unfold tailWord_487141
  simp only [CollatzResearch.WordTrace]
  refine ⟨17767491928178828904253277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11844994618785885936168851 17767491928178828904253277)
  ·
    refine ⟨6662809473067060839094979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17767491928178828904253277 6662809473067060839094979)
    ·
      refine ⟨9994214209600591258642469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6662809473067060839094979 9994214209600591258642469)
      ·
        refine ⟨1873915164300110860995463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9994214209600591258642469 1873915164300110860995463)
        ·
          refine ⟨2810872746450166291493195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1873915164300110860995463 2810872746450166291493195)
          ·
            refine ⟨4216309119675249437239793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2810872746450166291493195 4216309119675249437239793)
            ·
              refine ⟨3162231839756437077929845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4216309119675249437239793 3162231839756437077929845)
              ·
                refine ⟨296459234977165976055923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3162231839756437077929845 296459234977165976055923)
                ·
                  refine ⟨444688852465748964083885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 296459234977165976055923 444688852465748964083885)
                  ·
                    refine ⟨166758319674655861531457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 444688852465748964083885 166758319674655861531457)
                    ·
                      rfl

theorem cell22_487141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 5, 1, 3].length) (baseStart_487141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_487141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_487141 prefixEnd_487141 := by exact prefixLift 487141
  have htrace : WordTrace (prefixWord ++ tailWord_487141) baseStart_487141 baseEnd_487141 := by
    simpa [prefixWord, tailWord_487141, baseEnd_487141] using wordTrace_append hprefix tailTrace_487141
  have hstable : (prefixWord ++ tailWord_487141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487141).length < 2 ^ (prefixWord ++ tailWord_487141).sum := by decide
  have hdescent : baseEnd_487141 < baseStart_487141 := by decide
  rcases family_descends (prefixWord ++ tailWord_487141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487154 : List Nat := [3, 2, 1, 3, 1, 1, 4, 2, 5]
def baseStart_487154 : Nat := 118140960795 + 487154 * 2 ^ 59
def prefixEnd_487154 : Nat := 4983230072969 + 3 ^ 40 * 487154 * 2
def baseEnd_487154 : Nat := 55587589946776053652139

theorem tailTrace_487154 : CollatzResearch.WordTrace tailWord_487154 prefixEnd_487154 55587589946776053652139 := by
  unfold tailWord_487154
  simp only [CollatzResearch.WordTrace]
  refine ⟨4441991519282933031119129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11845310718087821416317677 4441991519282933031119129)
  ·
    refine ⟨3331493639462199773339347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4441991519282933031119129 3331493639462199773339347)
    ·
      refine ⟨4997240459193299660009021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3331493639462199773339347 4997240459193299660009021)
      ·
        refine ⟨1873965172197487372503383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4997240459193299660009021 1873965172197487372503383)
        ·
          refine ⟨2810947758296231058755075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1873965172197487372503383 2810947758296231058755075)
          ·
            refine ⟨4216421637444346588132613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2810947758296231058755075 4216421637444346588132613)
            ·
              refine ⟨790579057020814985274865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4216421637444346588132613 790579057020814985274865)
              ·
                refine ⟨592934292765611238956149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 790579057020814985274865 592934292765611238956149)
                ·
                  refine ⟨55587589946776053652139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 592934292765611238956149 55587589946776053652139)
                  ·
                    rfl

theorem cell22_487154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 2, 5].length) (baseStart_487154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_487154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_487154 prefixEnd_487154 := by exact prefixLift 487154
  have htrace : WordTrace (prefixWord ++ tailWord_487154) baseStart_487154 baseEnd_487154 := by
    simpa [prefixWord, tailWord_487154, baseEnd_487154] using wordTrace_append hprefix tailTrace_487154
  have hstable : (prefixWord ++ tailWord_487154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487154).length < 2 ^ (prefixWord ++ tailWord_487154).sum := by decide
  have hdescent : baseEnd_487154 < baseStart_487154 := by decide
  rcases family_descends (prefixWord ++ tailWord_487154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487156 : List Nat := [2, 6, 1, 1, 1, 1, 1, 1, 2, 6]
def baseStart_487156 : Nat := 118140960795 + 487156 * 2 ^ 59
def prefixEnd_487156 : Nat := 4983230072969 + 3 ^ 40 * 487156 * 2
def baseEnd_487156 : Nat := 166763454481200822406411

theorem tailTrace_487156 : CollatzResearch.WordTrace tailWord_487156 prefixEnd_487156 166763454481200822406411 := by
  unfold tailWord_487156
  simp only [CollatzResearch.WordTrace]
  refine ⟨8884019511562243233024661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11845359348749657644032881 8884019511562243233024661)
  ·
    refine ⟨416438414604480151548031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8884019511562243233024661 416438414604480151548031)
    ·
      refine ⟨624657621906720227322047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416438414604480151548031 624657621906720227322047)
      ·
        refine ⟨936986432860080340983071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 624657621906720227322047 936986432860080340983071)
        ·
          refine ⟨1405479649290120511474607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 936986432860080340983071 1405479649290120511474607)
          ·
            refine ⟨2108219473935180767211911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1405479649290120511474607 2108219473935180767211911)
            ·
              refine ⟨3162329210902771150817867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2108219473935180767211911 3162329210902771150817867)
              ·
                refine ⟨4743493816354156726226801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3162329210902771150817867 4743493816354156726226801)
                ·
                  refine ⟨3557620362265617544670101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4743493816354156726226801 3557620362265617544670101)
                  ·
                    refine ⟨166763454481200822406411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3557620362265617544670101 166763454481200822406411)
                    ·
                      rfl

theorem cell22_487156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_487156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_487156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_487156 prefixEnd_487156 := by exact prefixLift 487156
  have htrace : WordTrace (prefixWord ++ tailWord_487156) baseStart_487156 baseEnd_487156 := by
    simpa [prefixWord, tailWord_487156, baseEnd_487156] using wordTrace_append hprefix tailTrace_487156
  have hstable : (prefixWord ++ tailWord_487156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487156).length < 2 ^ (prefixWord ++ tailWord_487156).sum := by decide
  have hdescent : baseEnd_487156 < baseStart_487156 := by decide
  rcases family_descends (prefixWord ++ tailWord_487156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487158 : List Nat := [5, 1, 1, 1, 1, 4, 1, 4, 1, 3]
def baseStart_487158 : Nat := 118140960795 + 487158 * 2 ^ 59
def prefixEnd_487158 : Nat := 4983230072969 + 3 ^ 40 * 487158 * 2
def baseEnd_487158 : Nat := 166764139122073483856405

theorem tailTrace_487158 : CollatzResearch.WordTrace tailWord_487158 prefixEnd_487158 166764139122073483856405 := by
  unfold tailWord_487158
  simp only [CollatzResearch.WordTrace]
  refine ⟨1110506998069827550476383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11845407979411493871748085 1110506998069827550476383)
  ·
    refine ⟨1665760497104741325714575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1110506998069827550476383 1665760497104741325714575)
    ·
      refine ⟨2498640745657111988571863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1665760497104741325714575 2498640745657111988571863)
      ·
        refine ⟨3747961118485667982857795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2498640745657111988571863 3747961118485667982857795)
        ·
          refine ⟨5621941677728501974286693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3747961118485667982857795 5621941677728501974286693)
          ·
            refine ⟨1054114064574094120178755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5621941677728501974286693 1054114064574094120178755)
            ·
              refine ⟨1581171096861141180268133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1054114064574094120178755 1581171096861141180268133)
              ·
                refine ⟨296469580661463971300275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1581171096861141180268133 296469580661463971300275)
                ·
                  refine ⟨444704370992195956950413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 296469580661463971300275 444704370992195956950413)
                  ·
                    refine ⟨166764139122073483856405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 444704370992195956950413 166764139122073483856405)
                    ·
                      rfl

theorem cell22_487158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 4, 1, 3].length) (baseStart_487158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_487158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_487158 prefixEnd_487158 := by exact prefixLift 487158
  have htrace : WordTrace (prefixWord ++ tailWord_487158) baseStart_487158 baseEnd_487158 := by
    simpa [prefixWord, tailWord_487158, baseEnd_487158] using wordTrace_append hprefix tailTrace_487158
  have hstable : (prefixWord ++ tailWord_487158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487158).length < 2 ^ (prefixWord ++ tailWord_487158).sum := by decide
  have hdescent : baseEnd_487158 < baseStart_487158 := by decide
  rcases family_descends (prefixWord ++ tailWord_487158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487167 : List Nat := [1, 1, 2, 2, 1, 3, 3, 2, 3, 4]
def baseStart_487167 : Nat := 118140960795 + 487167 * 2 ^ 59
def prefixEnd_487167 : Nat := 4983230072969 + 3 ^ 40 * 487167 * 2
def baseEnd_487167 : Nat := 166767220006000460381377

theorem tailTrace_487167 : CollatzResearch.WordTrace tailWord_487167 prefixEnd_487167 166767220006000460381377 := by
  unfold tailWord_487167
  simp only [CollatzResearch.WordTrace]
  refine ⟨17768440226084635344699755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11845626817389756896466503 17768440226084635344699755)
  ·
    refine ⟨26652660339126953017049633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17768440226084635344699755 26652660339126953017049633)
    ·
      refine ⟨19989495254345214762787225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26652660339126953017049633 19989495254345214762787225)
      ·
        refine ⟨14992121440758911072090419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19989495254345214762787225 14992121440758911072090419)
        ·
          refine ⟨22488182161138366608135629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14992121440758911072090419 22488182161138366608135629)
          ·
            refine ⟨8433068310426887478050861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22488182161138366608135629 8433068310426887478050861)
            ·
              refine ⟨3162400616410082804269073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8433068310426887478050861 3162400616410082804269073)
              ·
                refine ⟨2371800462307562103201805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3162400616410082804269073 2371800462307562103201805)
                ·
                  refine ⟨889425173365335788700677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2371800462307562103201805 889425173365335788700677)
                  ·
                    refine ⟨166767220006000460381377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 889425173365335788700677 166767220006000460381377)
                    ·
                      rfl

theorem cell22_487167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 3, 4].length) (baseStart_487167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_487167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_487167 prefixEnd_487167 := by exact prefixLift 487167
  have htrace : WordTrace (prefixWord ++ tailWord_487167) baseStart_487167 baseEnd_487167 := by
    simpa [prefixWord, tailWord_487167, baseEnd_487167] using wordTrace_append hprefix tailTrace_487167
  have hstable : (prefixWord ++ tailWord_487167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487167).length < 2 ^ (prefixWord ++ tailWord_487167).sum := by decide
  have hdescent : baseEnd_487167 < baseStart_487167 := by decide
  rcases family_descends (prefixWord ++ tailWord_487167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487182 : List Nat := [4, 1, 1, 2, 1, 1, 3, 1, 8]
def baseStart_487182 : Nat := 118140960795 + 487182 * 2 ^ 59
def prefixEnd_487182 : Nat := 4983230072969 + 3 ^ 40 * 487182 * 2
def baseEnd_487182 : Nat := 55590784937515140418777

theorem tailTrace_487182 : CollatzResearch.WordTrace tailWord_487182 prefixEnd_487182 55590784937515140418777 := by
  unfold tailWord_487182
  simp only [CollatzResearch.WordTrace]
  refine ⟨2221123415128786613311975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11845991547353528604330533 2221123415128786613311975)
  ·
    refine ⟨3331685122693179919967963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2221123415128786613311975 3331685122693179919967963)
    ·
      refine ⟨4997527684039769879951945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3331685122693179919967963 4997527684039769879951945)
      ·
        refine ⟨3748145763029827409963959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4997527684039769879951945 3748145763029827409963959)
        ·
          refine ⟨5622218644544741114945939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3748145763029827409963959 5622218644544741114945939)
          ·
            refine ⟨8433327966817111672418909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5622218644544741114945939 8433327966817111672418909)
            ·
              refine ⟨3162497987556416877157091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8433327966817111672418909 3162497987556416877157091)
              ·
                refine ⟨4743746981334625315735637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3162497987556416877157091 4743746981334625315735637)
                ·
                  refine ⟨55590784937515140418777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4743746981334625315735637 55590784937515140418777)
                  ·
                    rfl

theorem cell22_487182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 8].length) (baseStart_487182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_487182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_487182 prefixEnd_487182 := by exact prefixLift 487182
  have htrace : WordTrace (prefixWord ++ tailWord_487182) baseStart_487182 baseEnd_487182 := by
    simpa [prefixWord, tailWord_487182, baseEnd_487182] using wordTrace_append hprefix tailTrace_487182
  have hstable : (prefixWord ++ tailWord_487182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487182).length < 2 ^ (prefixWord ++ tailWord_487182).sum := by decide
  have hdescent : baseEnd_487182 < baseStart_487182 := by decide
  rcases family_descends (prefixWord ++ tailWord_487182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487201 : List Nat := [1, 2, 3, 2, 1, 3, 4, 1, 1, 4]
def baseStart_487201 : Nat := 118140960795 + 487201 * 2 ^ 59
def prefixEnd_487201 : Nat := 4983230072969 + 3 ^ 40 * 487201 * 2
def baseEnd_487201 : Nat := 166778858900835705031273

theorem tailTrace_487201 : CollatzResearch.WordTrace tailWord_487201 prefixEnd_487201 166778858900835705031273 := by
  unfold tailWord_487201
  simp only [CollatzResearch.WordTrace]
  refine ⟨17769680307961459151437457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11846453538640972767624971 17769680307961459151437457)
  ·
    refine ⟨13327260230971094363578093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17769680307961459151437457 13327260230971094363578093)
    ·
      refine ⟨4997722586614160386341785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13327260230971094363578093 4997722586614160386341785)
      ·
        refine ⟨3748291939960620289756339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4997722586614160386341785 3748291939960620289756339)
        ·
          refine ⟨5622437909940930434634509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3748291939960620289756339 5622437909940930434634509)
          ·
            refine ⟨2108414216227848912987941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5622437909940930434634509 2108414216227848912987941)
            ·
              refine ⟨395327665542721671185239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2108414216227848912987941 395327665542721671185239)
              ·
                refine ⟨592991498314082506777859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 395327665542721671185239 592991498314082506777859)
                ·
                  refine ⟨889487247471123760166789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 592991498314082506777859 889487247471123760166789)
                  ·
                    refine ⟨166778858900835705031273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 889487247471123760166789 166778858900835705031273)
                    ·
                      rfl

theorem cell22_487201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 4, 1, 1, 4].length) (baseStart_487201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_487201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_487201 prefixEnd_487201 := by exact prefixLift 487201
  have htrace : WordTrace (prefixWord ++ tailWord_487201) baseStart_487201 baseEnd_487201 := by
    simpa [prefixWord, tailWord_487201, baseEnd_487201] using wordTrace_append hprefix tailTrace_487201
  have hstable : (prefixWord ++ tailWord_487201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487201).length < 2 ^ (prefixWord ++ tailWord_487201).sum := by decide
  have hdescent : baseEnd_487201 < baseStart_487201 := by decide
  rcases family_descends (prefixWord ++ tailWord_487201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487229 : List Nat := [1, 4, 1, 4, 1, 1, 1, 2, 1, 6]
def baseStart_487229 : Nat := 118140960795 + 487229 * 2 ^ 59
def prefixEnd_487229 : Nat := 4983230072969 + 3 ^ 40 * 487229 * 2
def baseEnd_487229 : Nat := 166788443873052965331187

theorem tailTrace_487229 : CollatzResearch.WordTrace tailWord_487229 prefixEnd_487229 166788443873052965331187 := by
  unfold tailWord_487229
  simp only [CollatzResearch.WordTrace]
  refine ⟨17770701551860019933456741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11847134367906679955637827 17770701551860019933456741)
  ·
    refine ⟨3332006540973753737523139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17770701551860019933456741 3332006540973753737523139)
    ·
      refine ⟨4998009811460630606284709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3332006540973753737523139 4998009811460630606284709)
      ·
        refine ⟨937126839648868238678383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4998009811460630606284709 937126839648868238678383)
        ·
          refine ⟨1405690259473302358017575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 937126839648868238678383 1405690259473302358017575)
          ·
            refine ⟨2108535389209953537026363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1405690259473302358017575 2108535389209953537026363)
            ·
              refine ⟨3162803083814930305539545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2108535389209953537026363 3162803083814930305539545)
              ·
                refine ⟨2372102312861197729154659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3162803083814930305539545 2372102312861197729154659)
                ·
                  refine ⟨3558153469291796593731989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2372102312861197729154659 3558153469291796593731989)
                  ·
                    refine ⟨166788443873052965331187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3558153469291796593731989 166788443873052965331187)
                    ·
                      rfl

theorem cell22_487229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_487229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_487229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_487229 prefixEnd_487229 := by exact prefixLift 487229
  have htrace : WordTrace (prefixWord ++ tailWord_487229) baseStart_487229 baseEnd_487229 := by
    simpa [prefixWord, tailWord_487229, baseEnd_487229] using wordTrace_append hprefix tailTrace_487229
  have hstable : (prefixWord ++ tailWord_487229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487229).length < 2 ^ (prefixWord ++ tailWord_487229).sum := by decide
  have hdescent : baseEnd_487229 < baseStart_487229 := by decide
  rcases family_descends (prefixWord ++ tailWord_487229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487231 : List Nat := [1, 1, 2, 2, 6, 2, 1, 1, 1, 5]
def baseStart_487231 : Nat := 118140960795 + 487231 * 2 ^ 59
def prefixEnd_487231 : Nat := 4983230072969 + 3 ^ 40 * 487231 * 2
def baseEnd_487231 : Nat := 166789128513925626781181

theorem tailTrace_487231 : CollatzResearch.WordTrace tailWord_487231 prefixEnd_487231 166789128513925626781181 := by
  unfold tailWord_487231
  simp only [CollatzResearch.WordTrace]
  refine ⟨17770774497852774275029547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11847182998568516183353031 17770774497852774275029547)
  ·
    refine ⟨26656161746779161412544321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17770774497852774275029547 26656161746779161412544321)
    ·
      refine ⟨19992121310084371059408241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26656161746779161412544321 19992121310084371059408241)
      ·
        refine ⟨14994090982563278294556181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19992121310084371059408241 14994090982563278294556181)
        ·
          refine ⟨702848014807653670057321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14994090982563278294556181 702848014807653670057321)
          ·
            refine ⟨527136011105740252542991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 702848014807653670057321 527136011105740252542991)
            ·
              refine ⟨790704016658610378814487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 527136011105740252542991 790704016658610378814487)
              ·
                refine ⟨1186056024987915568221731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 790704016658610378814487 1186056024987915568221731)
                ·
                  refine ⟨1779084037481873352332597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1186056024987915568221731 1779084037481873352332597)
                  ·
                    refine ⟨166789128513925626781181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1779084037481873352332597 166789128513925626781181)
                    ·
                      rfl

theorem cell22_487231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 1, 1, 5].length) (baseStart_487231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_487231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_487231 prefixEnd_487231 := by exact prefixLift 487231
  have htrace : WordTrace (prefixWord ++ tailWord_487231) baseStart_487231 baseEnd_487231 := by
    simpa [prefixWord, tailWord_487231, baseEnd_487231] using wordTrace_append hprefix tailTrace_487231
  have hstable : (prefixWord ++ tailWord_487231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487231).length < 2 ^ (prefixWord ++ tailWord_487231).sum := by decide
  have hdescent : baseEnd_487231 < baseStart_487231 := by decide
  rcases family_descends (prefixWord ++ tailWord_487231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487242 : List Nat := [3, 1, 2, 1, 1, 1, 3, 1, 2, 7]
def baseStart_487242 : Nat := 118140960795 + 487242 * 2 ^ 59
def prefixEnd_487242 : Nat := 4983230072969 + 3 ^ 40 * 487242 * 2
def baseEnd_487242 : Nat := 166792894038725264756147

theorem tailTrace_487242 : CollatzResearch.WordTrace tailWord_487242 prefixEnd_487242 166792894038725264756147 := by
  unfold tailWord_487242
  simp only [CollatzResearch.WordTrace]
  refine ⟨4442793925203230788419995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11847450467208615435786653 4442793925203230788419995)
  ·
    refine ⟨6664190887804846182629993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4442793925203230788419995 6664190887804846182629993)
    ·
      refine ⟨4998143165853634636972495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6664190887804846182629993 4998143165853634636972495)
      ·
        refine ⟨7497214748780451955458743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4998143165853634636972495 7497214748780451955458743)
        ·
          refine ⟨11245822123170677933188115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7497214748780451955458743 11245822123170677933188115)
          ·
            refine ⟨16868733184756016899782173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11245822123170677933188115 16868733184756016899782173)
            ·
              refine ⟨6325774944283506337418315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16868733184756016899782173 6325774944283506337418315)
              ·
                refine ⟨9488662416425259506127473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6325774944283506337418315 9488662416425259506127473)
                ·
                  refine ⟨7116496812318944629595605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9488662416425259506127473 7116496812318944629595605)
                  ·
                    refine ⟨166792894038725264756147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7116496812318944629595605 166792894038725264756147)
                    ·
                      rfl

theorem cell22_487242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_487242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_487242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_487242 prefixEnd_487242 := by exact prefixLift 487242
  have htrace : WordTrace (prefixWord ++ tailWord_487242) baseStart_487242 baseEnd_487242 := by
    simpa [prefixWord, tailWord_487242, baseEnd_487242] using wordTrace_append hprefix tailTrace_487242
  have hstable : (prefixWord ++ tailWord_487242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487242).length < 2 ^ (prefixWord ++ tailWord_487242).sum := by decide
  have hdescent : baseEnd_487242 < baseStart_487242 := by decide
  rcases family_descends (prefixWord ++ tailWord_487242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487244 : List Nat := [2, 2, 1, 3, 4, 1, 1, 8]
def baseStart_487244 : Nat := 118140960795 + 487244 * 2 ^ 59
def prefixEnd_487244 : Nat := 4983230072969 + 3 ^ 40 * 487244 * 2
def baseEnd_487244 : Nat := 18532619853288658467349

theorem tailTrace_487244 : CollatzResearch.WordTrace tailWord_487244 prefixEnd_487244 18532619853288658467349 := by
  unfold tailWord_487244
  simp only [CollatzResearch.WordTrace]
  refine ⟨8885624323402838747626393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11847499097870451663501857 8885624323402838747626393)
  ·
    refine ⟨6664218242552129060719795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8885624323402838747626393 6664218242552129060719795)
    ·
      refine ⟨9996327363828193591079693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6664218242552129060719795 9996327363828193591079693)
      ·
        refine ⟨3748622761435572596654885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9996327363828193591079693 3748622761435572596654885)
        ·
          refine ⟨702866767769169861872791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3748622761435572596654885 702866767769169861872791)
          ·
            refine ⟨1054300151653754792809187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 702866767769169861872791 1054300151653754792809187)
            ·
              refine ⟨1581450227480632189213781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1054300151653754792809187 1581450227480632189213781)
              ·
                refine ⟨18532619853288658467349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1581450227480632189213781 18532619853288658467349)
                ·
                  rfl

theorem cell22_487244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 8].length) (baseStart_487244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_487244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_487244 prefixEnd_487244 := by exact prefixLift 487244
  have htrace : WordTrace (prefixWord ++ tailWord_487244) baseStart_487244 baseEnd_487244 := by
    simpa [prefixWord, tailWord_487244, baseEnd_487244] using wordTrace_append hprefix tailTrace_487244
  have hstable : (prefixWord ++ tailWord_487244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487244).length < 2 ^ (prefixWord ++ tailWord_487244).sum := by decide
  have hdescent : baseEnd_487244 < baseStart_487244 := by decide
  rcases family_descends (prefixWord ++ tailWord_487244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487276 : List Nat := [2, 2, 1, 1, 4, 2, 3, 1, 3, 3]
def baseStart_487276 : Nat := 118140960795 + 487276 * 2 ^ 59
def prefixEnd_487276 : Nat := 4983230072969 + 3 ^ 40 * 487276 * 2
def baseEnd_487276 : Nat := 166804532933560509406043

theorem tailTrace_487276 : CollatzResearch.WordTrace tailWord_487276 prefixEnd_487276 166804532933560509406043 := by
  unfold tailWord_487276
  simp only [CollatzResearch.WordTrace]
  refine ⟨8886207891344873480208841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11848277188459831306945121 8886207891344873480208841)
  ·
    refine ⟨6664655918508655110156631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8886207891344873480208841 6664655918508655110156631)
    ·
      refine ⟨9996983877762982665234947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6664655918508655110156631 9996983877762982665234947)
      ·
        refine ⟨14995475816644473997852421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9996983877762982665234947 14995475816644473997852421)
        ·
          refine ⟨2811651715620838874597329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14995475816644473997852421 2811651715620838874597329)
          ·
            refine ⟨2108738786715629155947997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2811651715620838874597329 2108738786715629155947997)
            ·
              refine ⟨790777045018360933480499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2108738786715629155947997 790777045018360933480499)
              ·
                refine ⟨1186165567527541400220749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 790777045018360933480499 1186165567527541400220749)
                ·
                  refine ⟨444812087822828025082781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1186165567527541400220749 444812087822828025082781)
                  ·
                    refine ⟨166804532933560509406043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 444812087822828025082781 166804532933560509406043)
                    ·
                      rfl

theorem cell22_487276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 3].length) (baseStart_487276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_487276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_487276 prefixEnd_487276 := by exact prefixLift 487276
  have htrace : WordTrace (prefixWord ++ tailWord_487276) baseStart_487276 baseEnd_487276 := by
    simpa [prefixWord, tailWord_487276, baseEnd_487276] using wordTrace_append hprefix tailTrace_487276
  have hstable : (prefixWord ++ tailWord_487276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487276).length < 2 ^ (prefixWord ++ tailWord_487276).sum := by decide
  have hdescent : baseEnd_487276 < baseStart_487276 := by decide
  rcases family_descends (prefixWord ++ tailWord_487276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487289 : List Nat := [1, 2, 1, 3, 2, 2, 3, 3, 5]
def baseStart_487289 : Nat := 118140960795 + 487289 * 2 ^ 59
def prefixEnd_487289 : Nat := 4983230072969 + 3 ^ 40 * 487289 * 2
def baseEnd_487289 : Nat := 55602994366410936277001

theorem tailTrace_487289 : CollatzResearch.WordTrace tailWord_487289 prefixEnd_487289 55602994366410936277001 := by
  unfold tailWord_487289
  simp only [CollatzResearch.WordTrace]
  refine ⟨17772889931642650180640921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11848593287761766787093947 17772889931642650180640921)
  ·
    refine ⟨13329667448731987635480691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17772889931642650180640921 13329667448731987635480691)
    ·
      refine ⟨19994501173097981453221037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13329667448731987635480691 19994501173097981453221037)
      ·
        refine ⟨7497937939911743044957889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19994501173097981453221037 7497937939911743044957889)
        ·
          refine ⟨5623453454933807283718417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7497937939911743044957889 5623453454933807283718417)
          ·
            refine ⟨4217590091200355462788813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5623453454933807283718417 4217590091200355462788813)
            ·
              refine ⟨1581596284200133298545805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4217590091200355462788813 1581596284200133298545805)
              ·
                refine ⟨593098606575049986954677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1581596284200133298545805 593098606575049986954677)
                ·
                  refine ⟨55602994366410936277001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 593098606575049986954677 55602994366410936277001)
                  ·
                    rfl

theorem cell22_487289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 3, 5].length) (baseStart_487289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_487289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_487289 prefixEnd_487289 := by exact prefixLift 487289
  have htrace : WordTrace (prefixWord ++ tailWord_487289) baseStart_487289 baseEnd_487289 := by
    simpa [prefixWord, tailWord_487289, baseEnd_487289] using wordTrace_append hprefix tailTrace_487289
  have hstable : (prefixWord ++ tailWord_487289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487289).length < 2 ^ (prefixWord ++ tailWord_487289).sum := by decide
  have hdescent : baseEnd_487289 < baseStart_487289 := by decide
  rcases family_descends (prefixWord ++ tailWord_487289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487327 : List Nat := [1, 1, 2, 5, 3, 2, 2, 2, 1, 3]
def baseStart_487327 : Nat := 118140960795 + 487327 * 2 ^ 59
def prefixEnd_487327 : Nat := 4983230072969 + 3 ^ 40 * 487327 * 2
def baseEnd_487327 : Nat := 166821991275813376380887

theorem tailTrace_487327 : CollatzResearch.WordTrace tailWord_487327 prefixEnd_487327 166821991275813376380887 := by
  unfold tailWord_487327
  simp only [CollatzResearch.WordTrace]
  refine ⟨17774275905504982670524235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11849517270336655113682823 17774275905504982670524235)
  ·
    refine ⟨26661413858257474005786353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17774275905504982670524235 26661413858257474005786353)
    ·
      refine ⟨19996060393693105504339765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26661413858257474005786353 19996060393693105504339765)
      ·
        refine ⟨1874630661908728641031853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19996060393693105504339765 1874630661908728641031853)
        ·
          refine ⟨702986498215773240386945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1874630661908728641031853 702986498215773240386945)
          ·
            refine ⟨527239873661829930290209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 702986498215773240386945 527239873661829930290209)
            ·
              refine ⟨395429905246372447717657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 527239873661829930290209 395429905246372447717657)
              ·
                refine ⟨296572428934779335788243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 395429905246372447717657 296572428934779335788243)
                ·
                  refine ⟨444858643402169003682365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 296572428934779335788243 444858643402169003682365)
                  ·
                    refine ⟨166821991275813376380887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 444858643402169003682365 166821991275813376380887)
                    ·
                      rfl

theorem cell22_487327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 2, 2, 1, 3].length) (baseStart_487327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_487327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_487327 prefixEnd_487327 := by exact prefixLift 487327
  have htrace : WordTrace (prefixWord ++ tailWord_487327) baseStart_487327 baseEnd_487327 := by
    simpa [prefixWord, tailWord_487327, baseEnd_487327] using wordTrace_append hprefix tailTrace_487327
  have hstable : (prefixWord ++ tailWord_487327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487327).length < 2 ^ (prefixWord ++ tailWord_487327).sum := by decide
  have hdescent : baseEnd_487327 < baseStart_487327 := by decide
  rcases family_descends (prefixWord ++ tailWord_487327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487368 : List Nat := [2, 1, 3, 1, 4, 2, 2, 3, 4]
def baseStart_487368 : Nat := 118140960795 + 487368 * 2 ^ 59
def prefixEnd_487368 : Nat := 4983230072969 + 3 ^ 40 * 487368 * 2
def baseEnd_487368 : Nat := 55612008804567645368587

theorem tailTrace_487368 : CollatzResearch.WordTrace tailWord_487368 prefixEnd_487368 55612008804567645368587 := by
  unfold tailWord_487368
  simp only [CollatzResearch.WordTrace]
  refine ⟨8887885649178223336383379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11850514198904297781844505 8887885649178223336383379)
  ·
    refine ⟨13331828473767335004575069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8887885649178223336383379 13331828473767335004575069)
    ·
      refine ⟨4999435677662750626715651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13331828473767335004575069 4999435677662750626715651)
      ·
        refine ⟨7499153516494125940073477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4999435677662750626715651 7499153516494125940073477)
        ·
          refine ⟨1406091284342648613763777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7499153516494125940073477 1406091284342648613763777)
          ·
            refine ⟨1054568463256986460322833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1406091284342648613763777 1054568463256986460322833)
            ·
              refine ⟨790926347442739845242125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1054568463256986460322833 790926347442739845242125)
              ·
                refine ⟨296597380291027441965797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 790926347442739845242125 296597380291027441965797)
                ·
                  refine ⟨55612008804567645368587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 296597380291027441965797 55612008804567645368587)
                  ·
                    rfl

theorem cell22_487368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 3, 4].length) (baseStart_487368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_487368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_487368 prefixEnd_487368 := by exact prefixLift 487368
  have htrace : WordTrace (prefixWord ++ tailWord_487368) baseStart_487368 baseEnd_487368 := by
    simpa [prefixWord, tailWord_487368, baseEnd_487368] using wordTrace_append hprefix tailTrace_487368
  have hstable : (prefixWord ++ tailWord_487368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487368).length < 2 ^ (prefixWord ++ tailWord_487368).sum := by decide
  have hdescent : baseEnd_487368 < baseStart_487368 := by decide
  rcases family_descends (prefixWord ++ tailWord_487368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487445 : List Nat := [1, 3, 2, 1, 5, 2, 1, 1, 3, 3]
def baseStart_487445 : Nat := 118140960795 + 487445 * 2 ^ 59
def prefixEnd_487445 : Nat := 4983230072969 + 3 ^ 40 * 487445 * 2
def baseEnd_487445 : Nat := 166862385087300401930525

theorem tailTrace_487445 : CollatzResearch.WordTrace tailWord_487445 prefixEnd_487445 166862385087300401930525 := by
  unfold tailWord_487445
  simp only [CollatzResearch.WordTrace]
  refine ⟨17778579719077488823319789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11852386479384992548879859 17778579719077488823319789)
  ·
    refine ⟨6666967394654058308744921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17778579719077488823319789 6666967394654058308744921)
    ·
      refine ⟨5000225545990543731558691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6666967394654058308744921 5000225545990543731558691)
      ·
        refine ⟨7500338318985815597338037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5000225545990543731558691 7500338318985815597338037)
        ·
          refine ⟨703156717404920212250441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7500338318985815597338037 703156717404920212250441)
          ·
            refine ⟨527367538053690159187831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 703156717404920212250441 527367538053690159187831)
            ·
              refine ⟨791051307080535238781747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 527367538053690159187831 791051307080535238781747)
              ·
                refine ⟨1186576960620802858172621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 791051307080535238781747 1186576960620802858172621)
                ·
                  refine ⟨444966360232801071814733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1186576960620802858172621 444966360232801071814733)
                  ·
                    refine ⟨166862385087300401930525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 444966360232801071814733 166862385087300401930525)
                    ·
                      rfl

theorem cell22_487445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 1, 3, 3].length) (baseStart_487445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_487445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_487445 prefixEnd_487445 := by exact prefixLift 487445
  have htrace : WordTrace (prefixWord ++ tailWord_487445) baseStart_487445 baseEnd_487445 := by
    simpa [prefixWord, tailWord_487445, baseEnd_487445] using wordTrace_append hprefix tailTrace_487445
  have hstable : (prefixWord ++ tailWord_487445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487445).length < 2 ^ (prefixWord ++ tailWord_487445).sum := by decide
  have hdescent : baseEnd_487445 < baseStart_487445 := by decide
  rcases family_descends (prefixWord ++ tailWord_487445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487471 : List Nat := [1, 1, 2, 1, 2, 1, 1, 8, 1, 4]
def baseStart_487471 : Nat := 118140960795 + 487471 * 2 ^ 59
def prefixEnd_487471 : Nat := 4983230072969 + 3 ^ 40 * 487471 * 2
def baseEnd_487471 : Nat := 166871285418645000780445

theorem tailTrace_487471 : CollatzResearch.WordTrace tailWord_487471 prefixEnd_487471 166871285418645000780445 := by
  unfold tailWord_487471
  simp only [CollatzResearch.WordTrace]
  refine ⟨17779528016983295263766267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11853018677988863509177511 17779528016983295263766267)
  ·
    refine ⟨26669292025474942895649401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17779528016983295263766267 26669292025474942895649401)
    ·
      refine ⟨20001969019106207171737051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26669292025474942895649401 20001969019106207171737051)
      ·
        refine ⟨30002953528659310757605577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20001969019106207171737051 30002953528659310757605577)
        ·
          refine ⟨22502215146494483068204183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30002953528659310757605577 22502215146494483068204183)
          ·
            refine ⟨33753322719741724602306275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22502215146494483068204183 33753322719741724602306275)
            ·
              refine ⟨50629984079612586903459413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33753322719741724602306275 50629984079612586903459413)
              ·
                refine ⟨593320125932960002774915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 50629984079612586903459413 593320125932960002774915)
                ·
                  refine ⟨889980188899440004162373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 593320125932960002774915 889980188899440004162373)
                  ·
                    refine ⟨166871285418645000780445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 889980188899440004162373 166871285418645000780445)
                    ·
                      rfl

theorem cell22_487471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 8, 1, 4].length) (baseStart_487471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_487471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_487471 prefixEnd_487471 := by exact prefixLift 487471
  have htrace : WordTrace (prefixWord ++ tailWord_487471) baseStart_487471 baseEnd_487471 := by
    simpa [prefixWord, tailWord_487471, baseEnd_487471] using wordTrace_append hprefix tailTrace_487471
  have hstable : (prefixWord ++ tailWord_487471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487471).length < 2 ^ (prefixWord ++ tailWord_487471).sum := by decide
  have hdescent : baseEnd_487471 < baseStart_487471 := by decide
  rcases family_descends (prefixWord ++ tailWord_487471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487582 : List Nat := [4, 3, 1, 1, 3, 2, 2, 6]
def baseStart_487582 : Nat := 118140960795 + 487582 * 2 ^ 59
def prefixEnd_487582 : Nat := 4983230072969 + 3 ^ 40 * 487582 * 2
def baseEnd_487582 : Nat := 18545475887453079028345

theorem tailTrace_487582 : CollatzResearch.WordTrace tailWord_487582 prefixEnd_487582 18545475887453079028345 := by
  unfold tailWord_487582
  simp only [CollatzResearch.WordTrace]
  refine ⟨2222947064947645152632125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11855717679720774147371333 2222947064947645152632125)
  ·
    refine ⟨833605149355366932237047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2222947064947645152632125 833605149355366932237047)
    ·
      refine ⟨1250407724033050398355571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 833605149355366932237047 1250407724033050398355571)
      ·
        refine ⟨1875611586049575597533357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1250407724033050398355571 1875611586049575597533357)
        ·
          refine ⟨703354344768590849075009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1875611586049575597533357 703354344768590849075009)
          ·
            refine ⟨527515758576443136806257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 703354344768590849075009 527515758576443136806257)
            ·
              refine ⟨395636818932332352604693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 527515758576443136806257 395636818932332352604693)
              ·
                refine ⟨18545475887453079028345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 395636818932332352604693 18545475887453079028345)
                ·
                  rfl

theorem cell22_487582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 2, 6].length) (baseStart_487582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_487582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_487582 prefixEnd_487582 := by exact prefixLift 487582
  have htrace : WordTrace (prefixWord ++ tailWord_487582) baseStart_487582 baseEnd_487582 := by
    simpa [prefixWord, tailWord_487582, baseEnd_487582] using wordTrace_append hprefix tailTrace_487582
  have hstable : (prefixWord ++ tailWord_487582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487582).length < 2 ^ (prefixWord ++ tailWord_487582).sum := by decide
  have hdescent : baseEnd_487582 < baseStart_487582 := by decide
  rcases family_descends (prefixWord ++ tailWord_487582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487614 : List Nat := [4, 2, 1, 1, 5, 1, 1, 1, 3, 3]
def baseStart_487614 : Nat := 118140960795 + 487614 * 2 ^ 59
def prefixEnd_487614 : Nat := 4983230072969 + 3 ^ 40 * 487614 * 2
def baseEnd_487614 : Nat := 166920237241040294455007

theorem tailTrace_487614 : CollatzResearch.WordTrace tailWord_487614 prefixEnd_487614 166920237241040294455007 := by
  unfold tailWord_487614
  simp only [CollatzResearch.WordTrace]
  refine ⟨2223092956933153835777737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11856495770310153790814597 2223092956933153835777737)
  ·
    refine ⟨1667319717699865376833303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2223092956933153835777737 1667319717699865376833303)
    ·
      refine ⟨2500979576549798065249955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1667319717699865376833303 2500979576549798065249955)
      ·
        refine ⟨3751469364824697097874933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2500979576549798065249955 3751469364824697097874933)
        ·
          refine ⟨351700252952315352925775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3751469364824697097874933 351700252952315352925775)
          ·
            refine ⟨527550379428473029388663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351700252952315352925775 527550379428473029388663)
            ·
              refine ⟨791325569142709544082995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 527550379428473029388663 791325569142709544082995)
              ·
                refine ⟨1186988353714064316124493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 791325569142709544082995 1186988353714064316124493)
                ·
                  refine ⟨445120632642774118546685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1186988353714064316124493 445120632642774118546685)
                  ·
                    refine ⟨166920237241040294455007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 445120632642774118546685 166920237241040294455007)
                    ·
                      rfl

theorem cell22_487614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 1, 3, 3].length) (baseStart_487614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_487614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_487614 prefixEnd_487614 := by exact prefixLift 487614
  have htrace : WordTrace (prefixWord ++ tailWord_487614) baseStart_487614 baseEnd_487614 := by
    simpa [prefixWord, tailWord_487614, baseEnd_487614] using wordTrace_append hprefix tailTrace_487614
  have hstable : (prefixWord ++ tailWord_487614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487614).length < 2 ^ (prefixWord ++ tailWord_487614).sum := by decide
  have hdescent : baseEnd_487614 < baseStart_487614 := by decide
  rcases family_descends (prefixWord ++ tailWord_487614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487640 : List Nat := [2, 1, 2, 2, 4, 1, 3, 2, 1, 4]
def baseStart_487640 : Nat := 118140960795 + 487640 * 2 ^ 59
def prefixEnd_487640 : Nat := 4983230072969 + 3 ^ 40 * 487640 * 2
def baseEnd_487640 : Nat := 166929137572384893304927

theorem tailTrace_487640 : CollatzResearch.WordTrace tailWord_487640 prefixEnd_487640 166929137572384893304927 := by
  unfold tailWord_487640
  simp only [CollatzResearch.WordTrace]
  refine ⟨8892845976685518563334187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11857127968914024751112249 8892845976685518563334187)
  ·
    refine ⟨13339268965028277845001281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8892845976685518563334187 13339268965028277845001281)
    ·
      refine ⟨10004451723771208383750961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13339268965028277845001281 10004451723771208383750961)
      ·
        refine ⟨7503338792828406287813221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10004451723771208383750961 7503338792828406287813221)
        ·
          refine ⟨1406876023655326178964979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7503338792828406287813221 1406876023655326178964979)
          ·
            refine ⟨2110314035482989268447469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1406876023655326178964979 2110314035482989268447469)
            ·
              refine ⟨791367763306120975667801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2110314035482989268447469 791367763306120975667801)
              ·
                refine ⟨593525822479590731750851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 791367763306120975667801 593525822479590731750851)
                ·
                  refine ⟨890288733719386097626277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 593525822479590731750851 890288733719386097626277)
                  ·
                    refine ⟨166929137572384893304927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 890288733719386097626277 166929137572384893304927)
                    ·
                      rfl

theorem cell22_487640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 2, 1, 4].length) (baseStart_487640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_487640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_487640 prefixEnd_487640 := by exact prefixLift 487640
  have htrace : WordTrace (prefixWord ++ tailWord_487640) baseStart_487640 baseEnd_487640 := by
    simpa [prefixWord, tailWord_487640, baseEnd_487640] using wordTrace_append hprefix tailTrace_487640
  have hstable : (prefixWord ++ tailWord_487640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487640).length < 2 ^ (prefixWord ++ tailWord_487640).sum := by decide
  have hdescent : baseEnd_487640 < baseStart_487640 := by decide
  rcases family_descends (prefixWord ++ tailWord_487640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487653 : List Nat := [1, 3, 1, 4, 2, 1, 1, 1, 3, 5]
def baseStart_487653 : Nat := 118140960795 + 487653 * 2 ^ 59
def prefixEnd_487653 : Nat := 4983230072969 + 3 ^ 40 * 487653 * 2
def baseEnd_487653 : Nat := 166933587738057192729887

theorem tailTrace_487653 : CollatzResearch.WordTrace tailWord_487653 prefixEnd_487653 166933587738057192729887 := by
  unfold tailWord_487653
  simp only [CollatzResearch.WordTrace]
  refine ⟨17786166102323940346891613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11857444068215960231261075 17786166102323940346891613)
  ·
    refine ⟨6669812288371477630084355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17786166102323940346891613 6669812288371477630084355)
    ·
      refine ⟨10004718432557216445126533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6669812288371477630084355 10004718432557216445126533)
      ·
        refine ⟨1875884706104478083461225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10004718432557216445126533 1875884706104478083461225)
        ·
          refine ⟨1406913529578358562595919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1875884706104478083461225 1406913529578358562595919)
          ·
            refine ⟨2110370294367537843893879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1406913529578358562595919 2110370294367537843893879)
            ·
              refine ⟨3165555441551306765840819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2110370294367537843893879 3165555441551306765840819)
              ·
                refine ⟨4748333162326960148761229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3165555441551306765840819 4748333162326960148761229)
                ·
                  refine ⟨1780624935872610055785461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4748333162326960148761229 1780624935872610055785461)
                  ·
                    refine ⟨166933587738057192729887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1780624935872610055785461 166933587738057192729887)
                    ·
                      rfl

theorem cell22_487653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 3, 5].length) (baseStart_487653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_487653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_487653 prefixEnd_487653 := by exact prefixLift 487653
  have htrace : WordTrace (prefixWord ++ tailWord_487653) baseStart_487653 baseEnd_487653 := by
    simpa [prefixWord, tailWord_487653, baseEnd_487653] using wordTrace_append hprefix tailTrace_487653
  have hstable : (prefixWord ++ tailWord_487653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487653).length < 2 ^ (prefixWord ++ tailWord_487653).sum := by decide
  have hdescent : baseEnd_487653 < baseStart_487653 := by decide
  rcases family_descends (prefixWord ++ tailWord_487653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487670 : List Nat := [5, 1, 1, 1, 1, 1, 2, 3, 4, 3]
def baseStart_487670 : Nat := 118140960795 + 487670 * 2 ^ 59
def prefixEnd_487670 : Nat := 4983230072969 + 3 ^ 40 * 487670 * 2
def baseEnd_487670 : Nat := 166939407185474815054835

theorem tailTrace_487670 : CollatzResearch.WordTrace tailWord_487670 prefixEnd_487670 166939407185474815054835 := by
  unfold tailWord_487670
  simp only [CollatzResearch.WordTrace]
  refine ⟨1111674133953897015641279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11857857428841568166840309 1111674133953897015641279)
  ·
    refine ⟨1667511200930845523461919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1111674133953897015641279 1667511200930845523461919)
    ·
      refine ⟨2501266801396268285192879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1667511200930845523461919 2501266801396268285192879)
      ·
        refine ⟨3751900202094402427789319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2501266801396268285192879 3751900202094402427789319)
        ·
          refine ⟨5627850303141603641683979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3751900202094402427789319 5627850303141603641683979)
          ·
            refine ⟨8441775454712405462525969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5627850303141603641683979 8441775454712405462525969)
            ·
              refine ⟨6331331591034304096894477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8441775454712405462525969 6331331591034304096894477)
              ·
                refine ⟨2374249346637864036335429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6331331591034304096894477 2374249346637864036335429)
                ·
                  refine ⟨445171752494599506812893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2374249346637864036335429 445171752494599506812893)
                  ·
                    refine ⟨166939407185474815054835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 445171752494599506812893 166939407185474815054835)
                    ·
                      rfl

theorem cell22_487670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_487670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_487670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_487670 prefixEnd_487670 := by exact prefixLift 487670
  have htrace : WordTrace (prefixWord ++ tailWord_487670) baseStart_487670 baseEnd_487670 := by
    simpa [prefixWord, tailWord_487670, baseEnd_487670] using wordTrace_append hprefix tailTrace_487670
  have hstable : (prefixWord ++ tailWord_487670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487670).length < 2 ^ (prefixWord ++ tailWord_487670).sum := by decide
  have hdescent : baseEnd_487670 < baseStart_487670 := by decide
  rcases family_descends (prefixWord ++ tailWord_487670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487687 : List Nat := [1, 1, 4, 5, 1, 1, 2, 1, 1, 5]
def baseStart_487687 : Nat := 118140960795 + 487687 * 2 ^ 59
def prefixEnd_487687 : Nat := 4983230072969 + 3 ^ 40 * 487687 * 2
def baseEnd_487687 : Nat := 166945226632892437379783

theorem tailTrace_487687 : CollatzResearch.WordTrace tailWord_487687 prefixEnd_487687 166945226632892437379783 := by
  unfold tailWord_487687
  simp only [CollatzResearch.WordTrace]
  refine ⟨17787406184200764153629315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11858270789467176102419543 17787406184200764153629315)
  ·
    refine ⟨26681109276301146230443973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17787406184200764153629315 26681109276301146230443973)
    ·
      refine ⟨5002707989306464918208245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26681109276301146230443973 5002707989306464918208245)
      ·
        refine ⟨469003873997481086082023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5002707989306464918208245 469003873997481086082023)
        ·
          refine ⟨703505810996221629123035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469003873997481086082023 703505810996221629123035)
          ·
            refine ⟨1055258716494332443684553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 703505810996221629123035 1055258716494332443684553)
            ·
              refine ⟨791444037370749332763415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1055258716494332443684553 791444037370749332763415)
              ·
                refine ⟨1187166056056123999145123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 791444037370749332763415 1187166056056123999145123)
                ·
                  refine ⟨1780749084084185998717685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1187166056056123999145123 1780749084084185998717685)
                  ·
                    refine ⟨166945226632892437379783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1780749084084185998717685 166945226632892437379783)
                    ·
                      rfl

theorem cell22_487687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 1, 1, 5].length) (baseStart_487687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_487687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_487687 prefixEnd_487687 := by exact prefixLift 487687
  have htrace : WordTrace (prefixWord ++ tailWord_487687) baseStart_487687 baseEnd_487687 := by
    simpa [prefixWord, tailWord_487687, baseEnd_487687] using wordTrace_append hprefix tailTrace_487687
  have hstable : (prefixWord ++ tailWord_487687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487687).length < 2 ^ (prefixWord ++ tailWord_487687).sum := by decide
  have hdescent : baseEnd_487687 < baseStart_487687 := by decide
  rcases family_descends (prefixWord ++ tailWord_487687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487728 : List Nat := [2, 1, 1, 1, 2, 2, 2, 6, 5]
def baseStart_487728 : Nat := 118140960795 + 487728 * 2 ^ 59
def prefixEnd_487728 : Nat := 4983230072969 + 3 ^ 40 * 487728 * 2
def baseEnd_487728 : Nat := 55653087256927332368219

theorem tailTrace_487728 : CollatzResearch.WordTrace tailWord_487728 prefixEnd_487728 55653087256927332368219 := by
  unfold tailWord_487728
  simp only [CollatzResearch.WordTrace]
  refine ⟨8894450788526114077935919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11859267718034818770581225 8894450788526114077935919)
  ·
    refine ⟨13341676182789171116903879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8894450788526114077935919 13341676182789171116903879)
    ·
      refine ⟨20012514274183756675355819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13341676182789171116903879 20012514274183756675355819)
      ·
        refine ⟨30018771411275635013033729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20012514274183756675355819 30018771411275635013033729)
        ·
          refine ⟨22514078558456726259775297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30018771411275635013033729 22514078558456726259775297)
          ·
            refine ⟨16885558918842544694831473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22514078558456726259775297 16885558918842544694831473)
            ·
              refine ⟨12664169189131908521123605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16885558918842544694831473 12664169189131908521123605)
              ·
                refine ⟨593632930740558211927669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12664169189131908521123605 593632930740558211927669)
                ·
                  refine ⟨55653087256927332368219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 593632930740558211927669 55653087256927332368219)
                  ·
                    rfl

theorem cell22_487728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 6, 5].length) (baseStart_487728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_487728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_487728 prefixEnd_487728 := by exact prefixLift 487728
  have htrace : WordTrace (prefixWord ++ tailWord_487728) baseStart_487728 baseEnd_487728 := by
    simpa [prefixWord, tailWord_487728, baseEnd_487728] using wordTrace_append hprefix tailTrace_487728
  have hstable : (prefixWord ++ tailWord_487728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487728).length < 2 ^ (prefixWord ++ tailWord_487728).sum := by decide
  have hdescent : baseEnd_487728 < baseStart_487728 := by decide
  rcases family_descends (prefixWord ++ tailWord_487728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487732 : List Nat := [2, 5, 1, 1, 1, 2, 1, 3, 3, 3]
def baseStart_487732 : Nat := 118140960795 + 487732 * 2 ^ 59
def prefixEnd_487732 : Nat := 4983230072969 + 3 ^ 40 * 487732 * 2
def baseEnd_487732 : Nat := 166960631052527320004645

theorem tailTrace_487732 : CollatzResearch.WordTrace tailWord_487732 prefixEnd_487732 166960631052527320004645 := by
  unfold tailWord_487732
  simp only [CollatzResearch.WordTrace]
  refine ⟨8894523734518868419508725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11859364979358491226011633 8894523734518868419508725)
  ·
    refine ⟨833861600111143914328943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8894523734518868419508725 833861600111143914328943)
    ·
      refine ⟨1250792400166715871493415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 833861600111143914328943 1250792400166715871493415)
      ·
        refine ⟨1876188600250073807240123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1250792400166715871493415 1876188600250073807240123)
        ·
          refine ⟨2814282900375110710860185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1876188600250073807240123 2814282900375110710860185)
          ·
            refine ⟨2110712175281333033145139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2814282900375110710860185 2110712175281333033145139)
            ·
              refine ⟨3166068262921999549717709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2110712175281333033145139 3166068262921999549717709)
              ·
                refine ⟨1187275598595749831144141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3166068262921999549717709 1187275598595749831144141)
                ·
                  refine ⟨445228349473406186679053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1187275598595749831144141 445228349473406186679053)
                  ·
                    refine ⟨166960631052527320004645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 445228349473406186679053 166960631052527320004645)
                    ·
                      rfl

theorem cell22_487732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_487732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_487732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_487732 prefixEnd_487732 := by exact prefixLift 487732
  have htrace : WordTrace (prefixWord ++ tailWord_487732) baseStart_487732 baseEnd_487732 := by
    simpa [prefixWord, tailWord_487732, baseEnd_487732] using wordTrace_append hprefix tailTrace_487732
  have hstable : (prefixWord ++ tailWord_487732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487732).length < 2 ^ (prefixWord ++ tailWord_487732).sum := by decide
  have hdescent : baseEnd_487732 < baseStart_487732 := by decide
  rcases family_descends (prefixWord ++ tailWord_487732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487743 : List Nat := [1, 1, 2, 2, 4, 1, 1, 3, 2, 5]
def baseStart_487743 : Nat := 118140960795 + 487743 * 2 ^ 59
def prefixEnd_487743 : Nat := 4983230072969 + 3 ^ 40 * 487743 * 2
def baseEnd_487743 : Nat := 166964396577326957979611

theorem tailTrace_487743 : CollatzResearch.WordTrace tailWord_487743 prefixEnd_487743 166964396577326957979611 := by
  unfold tailWord_487743
  simp only [CollatzResearch.WordTrace]
  refine ⟨17789448671997885717667883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11859632447998590478445255 17789448671997885717667883)
  ·
    refine ⟨26684173007996828576501825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17789448671997885717667883 26684173007996828576501825)
    ·
      refine ⟨20013129755997621432376369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26684173007996828576501825 20013129755997621432376369)
      ·
        refine ⟨15009847316998216074282277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20013129755997621432376369 15009847316998216074282277)
        ·
          refine ⟨2814346371937165513927927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15009847316998216074282277 2814346371937165513927927)
          ·
            refine ⟨4221519557905748270891891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2814346371937165513927927 4221519557905748270891891)
            ·
              refine ⟨6332279336858622406337837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4221519557905748270891891 6332279336858622406337837)
              ·
                refine ⟨2374604751321983402376689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6332279336858622406337837 2374604751321983402376689)
                ·
                  refine ⟨1780953563491487551782517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2374604751321983402376689 1780953563491487551782517)
                  ·
                    refine ⟨166964396577326957979611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1780953563491487551782517 166964396577326957979611)
                    ·
                      rfl

theorem cell22_487743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 2, 5].length) (baseStart_487743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_487743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_487743 prefixEnd_487743 := by exact prefixLift 487743
  have htrace : WordTrace (prefixWord ++ tailWord_487743) baseStart_487743 baseEnd_487743 := by
    simpa [prefixWord, tailWord_487743, baseEnd_487743] using wordTrace_append hprefix tailTrace_487743
  have hstable : (prefixWord ++ tailWord_487743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487743).length < 2 ^ (prefixWord ++ tailWord_487743).sum := by decide
  have hdescent : baseEnd_487743 < baseStart_487743 := by decide
  rcases family_descends (prefixWord ++ tailWord_487743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487775 : List Nat := [1, 1, 2, 3, 1, 2, 4, 3, 1, 4]
def baseStart_487775 : Nat := 118140960795 + 487775 * 2 ^ 59
def prefixEnd_487775 : Nat := 4983230072969 + 3 ^ 40 * 487775 * 2
def baseEnd_487775 : Nat := 166975350831289541179513

theorem tailTrace_487775 : CollatzResearch.WordTrace tailWord_487775 prefixEnd_487775 166975350831289541179513 := by
  unfold tailWord_487775
  simp only [CollatzResearch.WordTrace]
  refine ⟨17790615807881955182832779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11860410538587970121888519 17790615807881955182832779)
  ·
    refine ⟨26685923711822932774249169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17790615807881955182832779 26685923711822932774249169)
    ·
      refine ⟨20014442783867199580686877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26685923711822932774249169 20014442783867199580686877)
      ·
        refine ⟨7505416043950199842757579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20014442783867199580686877 7505416043950199842757579)
        ·
          refine ⟨11258124065925299764136369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7505416043950199842757579 11258124065925299764136369)
          ·
            refine ⟨8443593049443974823102277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11258124065925299764136369 8443593049443974823102277)
            ·
              refine ⟨1583173696770745279331677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8443593049443974823102277 1583173696770745279331677)
              ·
                refine ⟨593690136289029479749379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1583173696770745279331677 593690136289029479749379)
                ·
                  refine ⟨890535204433544219624069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 593690136289029479749379 890535204433544219624069)
                  ·
                    refine ⟨166975350831289541179513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 890535204433544219624069 166975350831289541179513)
                    ·
                      rfl

theorem cell22_487775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 3, 1, 4].length) (baseStart_487775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_487775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_487775 prefixEnd_487775 := by exact prefixLift 487775
  have htrace : WordTrace (prefixWord ++ tailWord_487775) baseStart_487775 baseEnd_487775 := by
    simpa [prefixWord, tailWord_487775, baseEnd_487775] using wordTrace_append hprefix tailTrace_487775
  have hstable : (prefixWord ++ tailWord_487775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487775).length < 2 ^ (prefixWord ++ tailWord_487775).sum := by decide
  have hdescent : baseEnd_487775 < baseStart_487775 := by decide
  rcases family_descends (prefixWord ++ tailWord_487775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487809 : List Nat := [1, 2, 4, 3, 1, 3, 1, 2, 1, 4]
def baseStart_487809 : Nat := 118140960795 + 487809 * 2 ^ 59
def prefixEnd_487809 : Nat := 4983230072969 + 3 ^ 40 * 487809 * 2
def baseEnd_487809 : Nat := 166986989726124785829409

theorem tailTrace_487809 : CollatzResearch.WordTrace tailWord_487809 prefixEnd_487809 166986989726124785829409 := by
  unfold tailWord_487809
  simp only [CollatzResearch.WordTrace]
  refine ⟨17791855889758778989570481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11861237259839185993046987 17791855889758778989570481)
  ·
    refine ⟨13343891917319084242177861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17791855889758778989570481 13343891917319084242177861)
    ·
      refine ⟨2501979734497328295408349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13343891917319084242177861 2501979734497328295408349)
      ·
        refine ⟨938242400436498110778131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2501979734497328295408349 938242400436498110778131)
        ·
          refine ⟨1407363600654747166167197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 938242400436498110778131 1407363600654747166167197)
          ·
            refine ⟨527761350245530187312699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1407363600654747166167197 527761350245530187312699)
            ·
              refine ⟨791642025368295280969049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 527761350245530187312699 791642025368295280969049)
              ·
                refine ⟨593731519026221460726787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 791642025368295280969049 593731519026221460726787)
                ·
                  refine ⟨890597278539332191090181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 593731519026221460726787 890597278539332191090181)
                  ·
                    refine ⟨166986989726124785829409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 890597278539332191090181 166986989726124785829409)
                    ·
                      rfl

theorem cell22_487809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_487809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_487809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_487809 prefixEnd_487809 := by exact prefixLift 487809
  have htrace : WordTrace (prefixWord ++ tailWord_487809) baseStart_487809 baseEnd_487809 := by
    simpa [prefixWord, tailWord_487809, baseEnd_487809] using wordTrace_append hprefix tailTrace_487809
  have hstable : (prefixWord ++ tailWord_487809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487809).length < 2 ^ (prefixWord ++ tailWord_487809).sum := by decide
  have hdescent : baseEnd_487809 < baseStart_487809 := by decide
  rcases family_descends (prefixWord ++ tailWord_487809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487820 : List Nat := [2, 2, 1, 2, 1, 4, 1, 3, 2, 4]
def baseStart_487820 : Nat := 118140960795 + 487820 * 2 ^ 59
def prefixEnd_487820 : Nat := 4983230072969 + 3 ^ 40 * 487820 * 2
def baseEnd_487820 : Nat := 166990755250924423804375

theorem tailTrace_487820 : CollatzResearch.WordTrace tailWord_487820 prefixEnd_487820 166990755250924423804375 := by
  unfold tailWord_487820
  simp only [CollatzResearch.WordTrace]
  refine ⟨8896128546359463934110457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11861504728479285245480609 8896128546359463934110457)
  ·
    refine ⟨6672096409769597950582843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8896128546359463934110457 6672096409769597950582843)
    ·
      refine ⟨10008144614654396925874265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6672096409769597950582843 10008144614654396925874265)
      ·
        refine ⟨7506108460990797694405699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10008144614654396925874265 7506108460990797694405699)
        ·
          refine ⟨11259162691486196541608549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7506108460990797694405699 11259162691486196541608549)
          ·
            refine ⟨2111093004653661851551603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11259162691486196541608549 2111093004653661851551603)
            ·
              refine ⟨3166639506980492777327405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2111093004653661851551603 3166639506980492777327405)
              ·
                refine ⟨1187489815117684791497777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3166639506980492777327405 1187489815117684791497777)
                ·
                  refine ⟨890617361338263593623333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1187489815117684791497777 890617361338263593623333)
                  ·
                    refine ⟨166990755250924423804375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 890617361338263593623333 166990755250924423804375)
                    ·
                      rfl

theorem cell22_487820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 3, 2, 4].length) (baseStart_487820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_487820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_487820 prefixEnd_487820 := by exact prefixLift 487820
  have htrace : WordTrace (prefixWord ++ tailWord_487820) baseStart_487820 baseEnd_487820 := by
    simpa [prefixWord, tailWord_487820, baseEnd_487820] using wordTrace_append hprefix tailTrace_487820
  have hstable : (prefixWord ++ tailWord_487820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487820).length < 2 ^ (prefixWord ++ tailWord_487820).sum := by decide
  have hdescent : baseEnd_487820 < baseStart_487820 := by decide
  rcases family_descends (prefixWord ++ tailWord_487820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487822 : List Nat := [4, 1, 1, 4, 1, 2, 1, 2, 1, 5]
def baseStart_487822 : Nat := 118140960795 + 487822 * 2 ^ 59
def prefixEnd_487822 : Nat := 4983230072969 + 3 ^ 40 * 487822 * 2
def baseEnd_487822 : Nat := 166991439891797085254369

theorem tailTrace_487822 : CollatzResearch.WordTrace tailWord_487822 prefixEnd_487822 166991439891797085254369 := by
  unfold tailWord_487822
  simp only [CollatzResearch.WordTrace]
  refine ⟨2224041254838960276224215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11861553359141121473195813 2224041254838960276224215)
  ·
    refine ⟨3336061882258440414336323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2224041254838960276224215 3336061882258440414336323)
    ·
      refine ⟨5004092823387660621504485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3336061882258440414336323 5004092823387660621504485)
      ·
        refine ⟨938267404385186366532091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5004092823387660621504485 938267404385186366532091)
        ·
          refine ⟨1407401106577779549798137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 938267404385186366532091 1407401106577779549798137)
          ·
            refine ⟨1055550829933334662348603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1407401106577779549798137 1055550829933334662348603)
            ·
              refine ⟨1583326244900001993522905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1055550829933334662348603 1583326244900001993522905)
              ·
                refine ⟨1187494683675001495142179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1583326244900001993522905 1187494683675001495142179)
                ·
                  refine ⟨1781242025512502242713269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1187494683675001495142179 1781242025512502242713269)
                  ·
                    refine ⟨166991439891797085254369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1781242025512502242713269 166991439891797085254369)
                    ·
                      rfl

theorem cell22_487822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_487822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_487822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_487822 prefixEnd_487822 := by exact prefixLift 487822
  have htrace : WordTrace (prefixWord ++ tailWord_487822) baseStart_487822 baseEnd_487822 := by
    simpa [prefixWord, tailWord_487822, baseEnd_487822] using wordTrace_append hprefix tailTrace_487822
  have hstable : (prefixWord ++ tailWord_487822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487822).length < 2 ^ (prefixWord ++ tailWord_487822).sum := by decide
  have hdescent : baseEnd_487822 < baseStart_487822 := by decide
  rcases family_descends (prefixWord ++ tailWord_487822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487914 : List Nat := [3, 1, 3, 1, 3, 2, 3, 1, 5]
def baseStart_487914 : Nat := 118140960795 + 487914 * 2 ^ 59
def prefixEnd_487914 : Nat := 4983230072969 + 3 ^ 40 * 487914 * 2
def baseEnd_487914 : Nat := 55674311123979837318029

theorem tailTrace_487914 : CollatzResearch.WordTrace tailWord_487914 prefixEnd_487914 55674311123979837318029 := by
  unfold tailWord_487914
  simp only [CollatzResearch.WordTrace]
  refine ⟨4448921388594595480535699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11863790369585587948095197 4448921388594595480535699)
  ·
    refine ⟨6673382082891893220803549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4448921388594595480535699 6673382082891893220803549)
    ·
      refine ⟨2502518281084459957801331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6673382082891893220803549 2502518281084459957801331)
      ·
        refine ⟨3753777421626689936701997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2502518281084459957801331 3753777421626689936701997)
        ·
          refine ⟨1407666533110008726263249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3753777421626689936701997 1407666533110008726263249)
          ·
            refine ⟨1055749899832506544697437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1407666533110008726263249 1055749899832506544697437)
            ·
              refine ⟨395906212437189954261539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1055749899832506544697437 395906212437189954261539)
              ·
                refine ⟨593859318655784931392309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 395906212437189954261539 593859318655784931392309)
                ·
                  refine ⟨55674311123979837318029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 593859318655784931392309 55674311123979837318029)
                  ·
                    rfl

theorem cell22_487914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 3, 1, 5].length) (baseStart_487914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_487914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_487914 prefixEnd_487914 := by exact prefixLift 487914
  have htrace : WordTrace (prefixWord ++ tailWord_487914) baseStart_487914 baseEnd_487914 := by
    simpa [prefixWord, tailWord_487914, baseEnd_487914] using wordTrace_append hprefix tailTrace_487914
  have hstable : (prefixWord ++ tailWord_487914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487914).length < 2 ^ (prefixWord ++ tailWord_487914).sum := by decide
  have hdescent : baseEnd_487914 < baseStart_487914 := by decide
  rcases family_descends (prefixWord ++ tailWord_487914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487957 : List Nat := [1, 3, 2, 1, 3, 1, 1, 3, 4, 3]
def baseStart_487957 : Nat := 118140960795 + 487957 * 2 ^ 59
def prefixEnd_487957 : Nat := 4983230072969 + 3 ^ 40 * 487957 * 2
def baseEnd_487957 : Nat := 167037653150701733128955

theorem tailTrace_487957 : CollatzResearch.WordTrace tailWord_487957 prefixEnd_487957 167037653150701733128955 := by
  unfold tailWord_487957
  simp only [CollatzResearch.WordTrace]
  refine ⟨17797253893222600265958125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11864835928815066843972083 17797253893222600265958125)
  ·
    refine ⟨6673970209958475099734297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17797253893222600265958125 6673970209958475099734297)
    ·
      refine ⟨5005477657468856324800723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6673970209958475099734297 5005477657468856324800723)
      ·
        refine ⟨7508216486203284487201085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5005477657468856324800723 7508216486203284487201085)
        ·
          refine ⟨2815581182326231682700407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7508216486203284487201085 2815581182326231682700407)
          ·
            refine ⟨4223371773489347524050611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2815581182326231682700407 4223371773489347524050611)
            ·
              refine ⟨6335057660234021286075917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4223371773489347524050611 6335057660234021286075917)
              ·
                refine ⟨2375646622587757982278469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6335057660234021286075917 2375646622587757982278469)
                ·
                  refine ⟨445433741735204621677213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2375646622587757982278469 445433741735204621677213)
                  ·
                    refine ⟨167037653150701733128955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 445433741735204621677213 167037653150701733128955)
                    ·
                      rfl

theorem cell22_487957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 4, 3].length) (baseStart_487957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_487957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_487957 prefixEnd_487957 := by exact prefixLift 487957
  have htrace : WordTrace (prefixWord ++ tailWord_487957) baseStart_487957 baseEnd_487957 := by
    simpa [prefixWord, tailWord_487957, baseEnd_487957] using wordTrace_append hprefix tailTrace_487957
  have hstable : (prefixWord ++ tailWord_487957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487957).length < 2 ^ (prefixWord ++ tailWord_487957).sum := by decide
  have hdescent : baseEnd_487957 < baseStart_487957 := by decide
  rcases family_descends (prefixWord ++ tailWord_487957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487985 : List Nat := [1, 2, 2, 3, 1, 1, 2, 1, 2, 7]
def baseStart_487985 : Nat := 118140960795 + 487985 * 2 ^ 59
def prefixEnd_487985 : Nat := 4983230072969 + 3 ^ 40 * 487985 * 2
def baseEnd_487985 : Nat := 167047238122918993428869

theorem tailTrace_487985 : CollatzResearch.WordTrace tailWord_487985 prefixEnd_487985 167047238122918993428869 := by
  unfold tailWord_487985
  simp only [CollatzResearch.WordTrace]
  refine ⟨17798275137121161047977409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11865516758080774031984939 17798275137121161047977409)
  ·
    refine ⟨13348706352840870785983057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17798275137121161047977409 13348706352840870785983057)
    ·
      refine ⟨10011529764630653089487293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13348706352840870785983057 10011529764630653089487293)
      ·
        refine ⟨3754323661736494908557735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10011529764630653089487293 3754323661736494908557735)
        ·
          refine ⟨5631485492604742362836603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3754323661736494908557735 5631485492604742362836603)
          ·
            refine ⟨8447228238907113544254905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5631485492604742362836603 8447228238907113544254905)
            ·
              refine ⟨6335421179180335158191179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8447228238907113544254905 6335421179180335158191179)
              ·
                refine ⟨9503131768770502737286769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6335421179180335158191179 9503131768770502737286769)
                ·
                  refine ⟨7127348826577877052965077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9503131768770502737286769 7127348826577877052965077)
                  ·
                    refine ⟨167047238122918993428869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7127348826577877052965077 167047238122918993428869)
                    ·
                      rfl

theorem cell22_487985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 7].length) (baseStart_487985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_487985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_487985 prefixEnd_487985 := by exact prefixLift 487985
  have htrace : WordTrace (prefixWord ++ tailWord_487985) baseStart_487985 baseEnd_487985 := by
    simpa [prefixWord, tailWord_487985, baseEnd_487985] using wordTrace_append hprefix tailTrace_487985
  have hstable : (prefixWord ++ tailWord_487985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487985).length < 2 ^ (prefixWord ++ tailWord_487985).sum := by decide
  have hdescent : baseEnd_487985 < baseStart_487985 := by decide
  rcases family_descends (prefixWord ++ tailWord_487985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488004 : List Nat := [2, 3, 5, 1, 11]
def baseStart_488004 : Nat := 118140960795 + 488004 * 2 ^ 59
def prefixEnd_488004 : Nat := 4983230072969 + 3 ^ 40 * 488004 * 2
def baseEnd_488004 : Nat := 687463959716910605777

theorem tailTrace_488004 : CollatzResearch.WordTrace tailWord_488004 prefixEnd_488004 687463959716910605777 := by
  unfold tailWord_488004
  simp only [CollatzResearch.WordTrace]
  refine ⟨8899484062026163646459533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11865978749368218195279377 8899484062026163646459533)
  ·
    refine ⟨3337306523259811367422325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8899484062026163646459533 3337306523259811367422325)
    ·
      refine ⟨312872486555607315695843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3337306523259811367422325 312872486555607315695843)
      ·
        refine ⟨469308729833410973543765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312872486555607315695843 469308729833410973543765)
        ·
          refine ⟨687463959716910605777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 469308729833410973543765 687463959716910605777)
          ·
            rfl

theorem cell22_488004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 11].length) (baseStart_488004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_488004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_488004 prefixEnd_488004 := by exact prefixLift 488004
  have htrace : WordTrace (prefixWord ++ tailWord_488004) baseStart_488004 baseEnd_488004 := by
    simpa [prefixWord, tailWord_488004, baseEnd_488004] using wordTrace_append hprefix tailTrace_488004
  have hstable : (prefixWord ++ tailWord_488004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488004).length < 2 ^ (prefixWord ++ tailWord_488004).sum := by decide
  have hdescent : baseEnd_488004 < baseStart_488004 := by decide
  rcases family_descends (prefixWord ++ tailWord_488004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488006 : List Nat := [6, 1, 1, 1, 2, 1, 2, 2, 2, 4]
def baseStart_488006 : Nat := 118140960795 + 488006 * 2 ^ 59
def prefixEnd_488006 : Nat := 4983230072969 + 3 ^ 40 * 488006 * 2
def baseEnd_488006 : Nat := 167054426852081938653805

theorem tailTrace_488006 : CollatzResearch.WordTrace tailWord_488006 prefixEnd_488006 167054426852081938653805 := by
  unfold tailWord_488006
  simp only [CollatzResearch.WordTrace]
  refine ⟨556220033438908801077871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11866027380030054422994581 556220033438908801077871)
  ·
    refine ⟨834330050158363201616807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 556220033438908801077871 834330050158363201616807)
    ·
      refine ⟨1251495075237544802425211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 834330050158363201616807 1251495075237544802425211)
      ·
        refine ⟨1877242612856317203637817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1251495075237544802425211 1877242612856317203637817)
        ·
          refine ⟨1407931959642237902728363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1877242612856317203637817 1407931959642237902728363)
          ·
            refine ⟨2111897939463356854092545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1407931959642237902728363 2111897939463356854092545)
            ·
              refine ⟨1583923454597517640569409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2111897939463356854092545 1583923454597517640569409)
              ·
                refine ⟨1187942590948138230427057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1583923454597517640569409 1187942590948138230427057)
                ·
                  refine ⟨890956943211103672820293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1187942590948138230427057 890956943211103672820293)
                  ·
                    refine ⟨167054426852081938653805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 890956943211103672820293 167054426852081938653805)
                    ·
                      rfl

theorem cell22_488006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_488006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_488006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_488006 prefixEnd_488006 := by exact prefixLift 488006
  have htrace : WordTrace (prefixWord ++ tailWord_488006) baseStart_488006 baseEnd_488006 := by
    simpa [prefixWord, tailWord_488006, baseEnd_488006] using wordTrace_append hprefix tailTrace_488006
  have hstable : (prefixWord ++ tailWord_488006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488006).length < 2 ^ (prefixWord ++ tailWord_488006).sum := by decide
  have hdescent : baseEnd_488006 < baseStart_488006 := by decide
  rcases family_descends (prefixWord ++ tailWord_488006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488015 : List Nat := [1, 1, 2, 1, 1, 2, 4, 3, 7]
def baseStart_488015 : Nat := 118140960795 + 488015 * 2 ^ 59
def prefixEnd_488015 : Nat := 4983230072969 + 3 ^ 40 * 488015 * 2
def baseEnd_488015 : Nat := 55685835912002971726259

theorem tailTrace_488015 : CollatzResearch.WordTrace tailWord_488015 prefixEnd_488015 55685835912002971726259 := by
  unfold tailWord_488015
  simp only [CollatzResearch.WordTrace]
  refine ⟨17799369327012476171569499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11866246218008317447712999 17799369327012476171569499)
  ·
    refine ⟨26699053990518714257354249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17799369327012476171569499 26699053990518714257354249)
    ·
      refine ⟨20024290492889035693015687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26699053990518714257354249 20024290492889035693015687)
      ·
        refine ⟨30036435739333553539523531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20024290492889035693015687 30036435739333553539523531)
        ·
          refine ⟨45054653609000330309285297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30036435739333553539523531 45054653609000330309285297)
          ·
            refine ⟨33790990206750247731963973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45054653609000330309285297 33790990206750247731963973)
            ·
              refine ⟨6335810663765671449743245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33790990206750247731963973 6335810663765671449743245)
              ·
                refine ⟨2375928998912126793653717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6335810663765671449743245 2375928998912126793653717)
                ·
                  refine ⟨55685835912002971726259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2375928998912126793653717 55685835912002971726259)
                  ·
                    rfl

theorem cell22_488015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 7].length) (baseStart_488015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_488015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_488015 prefixEnd_488015 := by exact prefixLift 488015
  have htrace : WordTrace (prefixWord ++ tailWord_488015) baseStart_488015 baseEnd_488015 := by
    simpa [prefixWord, tailWord_488015, baseEnd_488015] using wordTrace_append hprefix tailTrace_488015
  have hstable : (prefixWord ++ tailWord_488015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488015).length < 2 ^ (prefixWord ++ tailWord_488015).sum := by decide
  have hdescent : baseEnd_488015 < baseStart_488015 := by decide
  rcases family_descends (prefixWord ++ tailWord_488015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488032 : List Nat := [2, 1, 1, 3, 2, 1, 4, 3, 5]
def baseStart_488032 : Nat := 118140960795 + 488032 * 2 ^ 59
def prefixEnd_488032 : Nat := 4983230072969 + 3 ^ 40 * 488032 * 2
def baseEnd_488032 : Nat := 55687775727808845834575

theorem tailTrace_488032 : CollatzResearch.WordTrace tailWord_488032 prefixEnd_488032 55687775727808845834575 := by
  unfold tailWord_488032
  simp only [CollatzResearch.WordTrace]
  refine ⟨8899994683975444037469175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11866659578633925383292233 8899994683975444037469175)
  ·
    refine ⟨13349992025963166056203763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8899994683975444037469175 13349992025963166056203763)
    ·
      refine ⟨20024988038944749084305645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13349992025963166056203763 20024988038944749084305645)
      ·
        refine ⟨7509370514604280906614617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20024988038944749084305645 7509370514604280906614617)
        ·
          refine ⟨5632027885953210679960963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7509370514604280906614617 5632027885953210679960963)
          ·
            refine ⟨8448041828929816019941445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5632027885953210679960963 8448041828929816019941445)
            ·
              refine ⟨1584007842924340503739021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8448041828929816019941445 1584007842924340503739021)
              ·
                refine ⟨594002941096627688902133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1584007842924340503739021 594002941096627688902133)
                ·
                  refine ⟨55687775727808845834575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 594002941096627688902133 55687775727808845834575)
                  ·
                    rfl

theorem cell22_488032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 3, 5].length) (baseStart_488032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_488032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_488032 prefixEnd_488032 := by exact prefixLift 488032
  have htrace : WordTrace (prefixWord ++ tailWord_488032) baseStart_488032 baseEnd_488032 := by
    simpa [prefixWord, tailWord_488032, baseEnd_488032] using wordTrace_append hprefix tailTrace_488032
  have hstable : (prefixWord ++ tailWord_488032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488032).length < 2 ^ (prefixWord ++ tailWord_488032).sum := by decide
  have hdescent : baseEnd_488032 < baseStart_488032 := by decide
  rcases family_descends (prefixWord ++ tailWord_488032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488094 : List Nat := [4, 3, 1, 1, 1, 1, 1, 4, 6]
def baseStart_488094 : Nat := 118140960795 + 488094 * 2 ^ 59
def prefixEnd_488094 : Nat := 4983230072969 + 3 ^ 40 * 488094 * 2
def baseEnd_488094 : Nat := 55694850350159680817845

theorem tailTrace_488094 : CollatzResearch.WordTrace tailWord_488094 prefixEnd_488094 55694850350159680817845 := by
  unfold tailWord_488094
  simp only [CollatzResearch.WordTrace]
  refine ⟨2225281336715784082961917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11868167129150848442463557 2225281336715784082961917)
  ·
    refine ⟨834480501268419031110719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2225281336715784082961917 834480501268419031110719)
    ·
      refine ⟨1251720751902628546666079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 834480501268419031110719 1251720751902628546666079)
      ·
        refine ⟨1877581127853942819999119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1251720751902628546666079 1877581127853942819999119)
        ·
          refine ⟨2816371691780914229998679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1877581127853942819999119 2816371691780914229998679)
          ·
            refine ⟨4224557537671371344998019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2816371691780914229998679 4224557537671371344998019)
            ·
              refine ⟨6336836306507057017497029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4224557537671371344998019 6336836306507057017497029)
              ·
                refine ⟨1188156807470073190780693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6336836306507057017497029 1188156807470073190780693)
                ·
                  refine ⟨55694850350159680817845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1188156807470073190780693 55694850350159680817845)
                  ·
                    rfl

theorem cell22_488094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_488094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_488094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_488094 prefixEnd_488094 := by exact prefixLift 488094
  have htrace : WordTrace (prefixWord ++ tailWord_488094) baseStart_488094 baseEnd_488094 := by
    simpa [prefixWord, tailWord_488094, baseEnd_488094] using wordTrace_append hprefix tailTrace_488094
  have hstable : (prefixWord ++ tailWord_488094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488094).length < 2 ^ (prefixWord ++ tailWord_488094).sum := by decide
  have hdescent : baseEnd_488094 < baseStart_488094 := by decide
  rcases family_descends (prefixWord ++ tailWord_488094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488096 : List Nat := [2, 1, 1, 4, 4, 1, 2, 2, 1, 4]
def baseStart_488096 : Nat := 118140960795 + 488096 * 2 ^ 59
def prefixEnd_488096 : Nat := 4983230072969 + 3 ^ 40 * 488096 * 2
def baseEnd_488096 : Nat := 167085235691351703903529

theorem tailTrace_488096 : CollatzResearch.WordTrace tailWord_488096 prefixEnd_488096 167085235691351703903529 := by
  unfold tailWord_488096
  simp only [CollatzResearch.WordTrace]
  refine ⟨8901161819859513502634071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11868215759812684670178761 8901161819859513502634071)
  ·
    refine ⟨13351742729789270253951107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8901161819859513502634071 13351742729789270253951107)
    ·
      refine ⟨20027614094683905380926661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13351742729789270253951107 20027614094683905380926661)
      ·
        refine ⟨3755177642753232258923749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20027614094683905380926661 3755177642753232258923749)
        ·
          refine ⟨704095808016231048548203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3755177642753232258923749 704095808016231048548203)
          ·
            refine ⟨1056143712024346572822305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 704095808016231048548203 1056143712024346572822305)
            ·
              refine ⟨792107784018259929616729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1056143712024346572822305 792107784018259929616729)
              ·
                refine ⟨594080838013694947212547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 792107784018259929616729 594080838013694947212547)
                ·
                  refine ⟨891121257020542420818821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 594080838013694947212547 891121257020542420818821)
                  ·
                    refine ⟨167085235691351703903529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 891121257020542420818821 167085235691351703903529)
                    ·
                      rfl

theorem cell22_488096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 2, 1, 4].length) (baseStart_488096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_488096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_488096 prefixEnd_488096 := by exact prefixLift 488096
  have htrace : WordTrace (prefixWord ++ tailWord_488096) baseStart_488096 baseEnd_488096 := by
    simpa [prefixWord, tailWord_488096, baseEnd_488096] using wordTrace_append hprefix tailTrace_488096
  have hstable : (prefixWord ++ tailWord_488096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488096).length < 2 ^ (prefixWord ++ tailWord_488096).sum := by decide
  have hdescent : baseEnd_488096 < baseStart_488096 := by decide
  rcases family_descends (prefixWord ++ tailWord_488096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488111 : List Nat := [1, 1, 2, 1, 2, 7, 1, 3, 4]
def baseStart_488111 : Nat := 118140960795 + 488111 * 2 ^ 59
def prefixEnd_488111 : Nat := 4983230072969 + 3 ^ 40 * 488111 * 2
def baseEnd_488111 : Nat := 55696790165965554926161

theorem tailTrace_488111 : CollatzResearch.WordTrace tailWord_488111 prefixEnd_488111 55696790165965554926161 := by
  unfold tailWord_488111
  simp only [CollatzResearch.WordTrace]
  refine ⟨17802870734664684567064187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11868580489776456378042791 17802870734664684567064187)
  ·
    refine ⟨26704306101997026850596281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17802870734664684567064187 26704306101997026850596281)
    ·
      refine ⟨20028229576497770137947211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26704306101997026850596281 20028229576497770137947211)
      ·
        refine ⟨30042344364746655206920817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20028229576497770137947211 30042344364746655206920817)
        ·
          refine ⟨22531758273559991405190613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30042344364746655206920817 22531758273559991405190613)
          ·
            refine ⟨528088084536562298559155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 22531758273559991405190613 528088084536562298559155)
            ·
              refine ⟨792132126804843447838733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 528088084536562298559155 792132126804843447838733)
              ·
                refine ⟨297049547551816292939525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 792132126804843447838733 297049547551816292939525)
                ·
                  refine ⟨55696790165965554926161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 297049547551816292939525 55696790165965554926161)
                  ·
                    rfl

theorem cell22_488111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 3, 4].length) (baseStart_488111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_488111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_488111 prefixEnd_488111 := by exact prefixLift 488111
  have htrace : WordTrace (prefixWord ++ tailWord_488111) baseStart_488111 baseEnd_488111 := by
    simpa [prefixWord, tailWord_488111, baseEnd_488111] using wordTrace_append hprefix tailTrace_488111
  have hstable : (prefixWord ++ tailWord_488111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488111).length < 2 ^ (prefixWord ++ tailWord_488111).sum := by decide
  have hdescent : baseEnd_488111 < baseStart_488111 := by decide
  rcases family_descends (prefixWord ++ tailWord_488111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488124 : List Nat := [2, 2, 2, 3, 1, 1, 3, 2, 2, 4]
def baseStart_488124 : Nat := 118140960795 + 488124 * 2 ^ 59
def prefixEnd_488124 : Nat := 4983230072969 + 3 ^ 40 * 488124 * 2
def baseEnd_488124 : Nat := 167094820663568964203443

theorem tailTrace_488124 : CollatzResearch.WordTrace tailWord_488124 prefixEnd_488124 167094820663568964203443 := by
  unfold tailWord_488124
  simp only [CollatzResearch.WordTrace]
  refine ⟨8901672441808793893643713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11868896589078391858191617 8901672441808793893643713)
  ·
    refine ⟨6676254331356595420232785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8901672441808793893643713 6676254331356595420232785)
    ·
      refine ⟨5007190748517446565174589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6676254331356595420232785 5007190748517446565174589)
      ·
        refine ⟨1877696530694042461940471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5007190748517446565174589 1877696530694042461940471)
        ·
          refine ⟨2816544796041063692910707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1877696530694042461940471 2816544796041063692910707)
          ·
            refine ⟨4224817194061595539366061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2816544796041063692910707 4224817194061595539366061)
            ·
              refine ⟨1584306447773098327262273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4224817194061595539366061 1584306447773098327262273)
              ·
                refine ⟨1188229835829823745446705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1584306447773098327262273 1188229835829823745446705)
                ·
                  refine ⟨891172376872367809085029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1188229835829823745446705 891172376872367809085029)
                  ·
                    refine ⟨167094820663568964203443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 891172376872367809085029 167094820663568964203443)
                    ·
                      rfl

theorem cell22_488124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_488124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_488124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_488124 prefixEnd_488124 := by exact prefixLift 488124
  have htrace : WordTrace (prefixWord ++ tailWord_488124) baseStart_488124 baseEnd_488124 := by
    simpa [prefixWord, tailWord_488124, baseEnd_488124] using wordTrace_append hprefix tailTrace_488124
  have hstable : (prefixWord ++ tailWord_488124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488124).length < 2 ^ (prefixWord ++ tailWord_488124).sum := by decide
  have hdescent : baseEnd_488124 < baseStart_488124 := by decide
  rcases family_descends (prefixWord ++ tailWord_488124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488126 : List Nat := [4, 2, 1, 1, 2, 1, 2, 4, 2, 3]
def baseStart_488126 : Nat := 118140960795 + 488126 * 2 ^ 59
def prefixEnd_488126 : Nat := 4983230072969 + 3 ^ 40 * 488126 * 2
def baseEnd_488126 : Nat := 167095505304441625653437

theorem tailTrace_488126 : CollatzResearch.WordTrace tailWord_488126 prefixEnd_488126 167095505304441625653437 := by
  unfold tailWord_488126
  simp only [CollatzResearch.WordTrace]
  refine ⟨2225427228701292766107529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11868945219740228085906821 2225427228701292766107529)
  ·
    refine ⟨1669070421525969574580647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2225427228701292766107529 1669070421525969574580647)
    ·
      refine ⟨2503605632288954361870971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1669070421525969574580647 2503605632288954361870971)
      ·
        refine ⟨3755408448433431542806457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2503605632288954361870971 3755408448433431542806457)
        ·
          refine ⟨2816556336325073657104843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3755408448433431542806457 2816556336325073657104843)
          ·
            refine ⟨4224834504487610485657265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2816556336325073657104843 4224834504487610485657265)
            ·
              refine ⟨3168625878365707864242949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4224834504487610485657265 3168625878365707864242949)
              ·
                refine ⟨594117352193570224545553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3168625878365707864242949 594117352193570224545553)
                ·
                  refine ⟨445588014145177668409165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 594117352193570224545553 445588014145177668409165)
                  ·
                    refine ⟨167095505304441625653437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 445588014145177668409165 167095505304441625653437)
                    ·
                      rfl

theorem cell22_488126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_488126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_488126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_488126 prefixEnd_488126 := by exact prefixLift 488126
  have htrace : WordTrace (prefixWord ++ tailWord_488126) baseStart_488126 baseEnd_488126 := by
    simpa [prefixWord, tailWord_488126, baseEnd_488126] using wordTrace_append hprefix tailTrace_488126
  have hstable : (prefixWord ++ tailWord_488126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488126).length < 2 ^ (prefixWord ++ tailWord_488126).sum := by decide
  have hdescent : baseEnd_488126 < baseStart_488126 := by decide
  rcases family_descends (prefixWord ++ tailWord_488126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488154 : List Nat := [3, 1, 1, 2, 2, 2, 2, 1, 5, 3]
def baseStart_488154 : Nat := 118140960795 + 488154 * 2 ^ 59
def prefixEnd_488154 : Nat := 4983230072969 + 3 ^ 40 * 488154 * 2
def baseEnd_488154 : Nat := 167105090276658885953351

theorem tailTrace_488154 : CollatzResearch.WordTrace tailWord_488154 prefixEnd_488154 167105090276658885953351 := by
  unfold tailWord_488154
  simp only [CollatzResearch.WordTrace]
  refine ⟨4451109768377225727719879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11869626049005935273919677 4451109768377225727719879)
  ·
    refine ⟨6676664652565838591579819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4451109768377225727719879 6676664652565838591579819)
    ·
      refine ⟨10014996978848757887369729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6676664652565838591579819 10014996978848757887369729)
      ·
        refine ⟨7511247734136568415527297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10014996978848757887369729 7511247734136568415527297)
        ·
          refine ⟨5633435800602426311645473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7511247734136568415527297 5633435800602426311645473)
          ·
            refine ⟨4225076850451819733734105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5633435800602426311645473 4225076850451819733734105)
            ·
              refine ⟨3168807637838864800300579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4225076850451819733734105 3168807637838864800300579)
              ·
                refine ⟨4753211456758297200450869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3168807637838864800300579 4753211456758297200450869)
                ·
                  refine ⟨445613574071090362542269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4753211456758297200450869 445613574071090362542269)
                  ·
                    refine ⟨167105090276658885953351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 445613574071090362542269 167105090276658885953351)
                    ·
                      rfl

theorem cell22_488154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 5, 3].length) (baseStart_488154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_488154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_488154 prefixEnd_488154 := by exact prefixLift 488154
  have htrace : WordTrace (prefixWord ++ tailWord_488154) baseStart_488154 baseEnd_488154 := by
    simpa [prefixWord, tailWord_488154, baseEnd_488154] using wordTrace_append hprefix tailTrace_488154
  have hstable : (prefixWord ++ tailWord_488154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488154).length < 2 ^ (prefixWord ++ tailWord_488154).sum := by decide
  have hdescent : baseEnd_488154 < baseStart_488154 := by decide
  rcases family_descends (prefixWord ++ tailWord_488154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488171 : List Nat := [1, 1, 1, 1, 2, 4, 1, 7, 1, 3]
def baseStart_488171 : Nat := 118140960795 + 488171 * 2 ^ 59
def prefixEnd_488171 : Nat := 4983230072969 + 3 ^ 40 * 488171 * 2
def baseEnd_488171 : Nat := 167110909724076508278299

theorem tailTrace_488171 : CollatzResearch.WordTrace tailWord_488171 prefixEnd_488171 167110909724076508278299 := by
  unfold tailWord_488171
  simp only [CollatzResearch.WordTrace]
  refine ⟨17805059114447314814248367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11870039409631543209498911 17805059114447314814248367)
  ·
    refine ⟨26707588671670972221372551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17805059114447314814248367 26707588671670972221372551)
    ·
      refine ⟨40061383007506458332058827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26707588671670972221372551 40061383007506458332058827)
      ·
        refine ⟨60092074511259687498088241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40061383007506458332058827 60092074511259687498088241)
        ·
          refine ⟨45069055883444765623566181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60092074511259687498088241 45069055883444765623566181)
          ·
            refine ⟨8450447978145893554418659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45069055883444765623566181 8450447978145893554418659)
            ·
              refine ⟨12675671967218840331627989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8450447978145893554418659 12675671967218840331627989)
              ·
                refine ⟨297086061731691570272531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 12675671967218840331627989 297086061731691570272531)
                ·
                  refine ⟨445629092597537355408797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 297086061731691570272531 445629092597537355408797)
                  ·
                    refine ⟨167110909724076508278299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 445629092597537355408797 167110909724076508278299)
                    ·
                      rfl

theorem cell22_488171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 7, 1, 3].length) (baseStart_488171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_488171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_488171 prefixEnd_488171 := by exact prefixLift 488171
  have htrace : WordTrace (prefixWord ++ tailWord_488171) baseStart_488171 baseEnd_488171 := by
    simpa [prefixWord, tailWord_488171, baseEnd_488171] using wordTrace_append hprefix tailTrace_488171
  have hstable : (prefixWord ++ tailWord_488171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488171).length < 2 ^ (prefixWord ++ tailWord_488171).sum := by decide
  have hdescent : baseEnd_488171 < baseStart_488171 := by decide
  rcases family_descends (prefixWord ++ tailWord_488171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488184 : List Nat := [2, 1, 2, 1, 1, 2, 6, 2, 5]
def baseStart_488184 : Nat := 118140960795 + 488184 * 2 ^ 59
def prefixEnd_488184 : Nat := 4983230072969 + 3 ^ 40 * 488184 * 2
def baseEnd_488184 : Nat := 55705119963249602567753

theorem tailTrace_488184 : CollatzResearch.WordTrace tailWord_488184 prefixEnd_488184 55705119963249602567753 := by
  unfold tailWord_488184
  simp only [CollatzResearch.WordTrace]
  refine ⟨8902766631700109017235803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11870355508933478689647737 8902766631700109017235803)
  ·
    refine ⟨13354149947550163525853705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8902766631700109017235803 13354149947550163525853705)
    ·
      refine ⟨10015612460662622644390279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13354149947550163525853705 10015612460662622644390279)
      ·
        refine ⟨15023418690993933966585419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10015612460662622644390279 15023418690993933966585419)
        ·
          refine ⟨22535128036490900949878129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15023418690993933966585419 22535128036490900949878129)
          ·
            refine ⟨16901346027368175712408597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22535128036490900949878129 16901346027368175712408597)
            ·
              refine ⟨792250595032883236519153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16901346027368175712408597 792250595032883236519153)
              ·
                refine ⟨594187946274662427389365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 792250595032883236519153 594187946274662427389365)
                ·
                  refine ⟨55705119963249602567753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 594187946274662427389365 55705119963249602567753)
                  ·
                    rfl

theorem cell22_488184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 2, 5].length) (baseStart_488184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_488184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_488184 prefixEnd_488184 := by exact prefixLift 488184
  have htrace : WordTrace (prefixWord ++ tailWord_488184) baseStart_488184 baseEnd_488184 := by
    simpa [prefixWord, tailWord_488184, baseEnd_488184] using wordTrace_append hprefix tailTrace_488184
  have hstable : (prefixWord ++ tailWord_488184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488184).length < 2 ^ (prefixWord ++ tailWord_488184).sum := by decide
  have hdescent : baseEnd_488184 < baseStart_488184 := by decide
  rcases family_descends (prefixWord ++ tailWord_488184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488188 : List Nat := [2, 2, 2, 1, 3, 3, 1, 4, 1, 3]
def baseStart_488188 : Nat := 118140960795 + 488188 * 2 ^ 59
def prefixEnd_488188 : Nat := 4983230072969 + 3 ^ 40 * 488188 * 2
def baseEnd_488188 : Nat := 167116729171494130603247

theorem tailTrace_488188 : CollatzResearch.WordTrace tailWord_488188 prefixEnd_488188 167116729171494130603247 := by
  unfold tailWord_488188
  simp only [CollatzResearch.WordTrace]
  refine ⟨8902839577692863358808609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11870452770257151145078145 8902839577692863358808609)
  ·
    refine ⟨6677129683269647519106457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8902839577692863358808609 6677129683269647519106457)
    ·
      refine ⟨5007847262452235639329843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6677129683269647519106457 5007847262452235639329843)
      ·
        refine ⟨7511770893678353458994765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5007847262452235639329843 7511770893678353458994765)
        ·
          refine ⟨2816914085129382547123037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7511770893678353458994765 2816914085129382547123037)
          ·
            refine ⟨1056342781923518455171139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2816914085129382547123037 1056342781923518455171139)
            ·
              refine ⟨1584514172885277682756709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1056342781923518455171139 1584514172885277682756709)
              ·
                refine ⟨297096407415989565516883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1584514172885277682756709 297096407415989565516883)
                ·
                  refine ⟨445644611123984348275325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 297096407415989565516883 445644611123984348275325)
                  ·
                    refine ⟨167116729171494130603247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 445644611123984348275325 167116729171494130603247)
                    ·
                      rfl

theorem cell22_488188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 4, 1, 3].length) (baseStart_488188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_488188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_488188 prefixEnd_488188 := by exact prefixLift 488188
  have htrace : WordTrace (prefixWord ++ tailWord_488188) baseStart_488188 baseEnd_488188 := by
    simpa [prefixWord, tailWord_488188, baseEnd_488188] using wordTrace_append hprefix tailTrace_488188
  have hstable : (prefixWord ++ tailWord_488188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488188).length < 2 ^ (prefixWord ++ tailWord_488188).sum := by decide
  have hdescent : baseEnd_488188 < baseStart_488188 := by decide
  rcases family_descends (prefixWord ++ tailWord_488188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488199 : List Nat := [1, 1, 4, 4, 1, 1, 1, 1, 1, 7]
def baseStart_488199 : Nat := 118140960795 + 488199 * 2 ^ 59
def prefixEnd_488199 : Nat := 4983230072969 + 3 ^ 40 * 488199 * 2
def baseEnd_488199 : Nat := 167120494696293768578213

theorem tailTrace_488199 : CollatzResearch.WordTrace tailWord_488199 prefixEnd_488199 167120494696293768578213 := by
  unfold tailWord_488199
  simp only [CollatzResearch.WordTrace]
  refine ⟨17806080358345875596267651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11870720238897250397511767 17806080358345875596267651)
  ·
    refine ⟨26709120537518813394401477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17806080358345875596267651 26709120537518813394401477)
    ·
      refine ⟨5007960100784777511450277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26709120537518813394401477 5007960100784777511450277)
      ·
        refine ⟨938992518897145783396927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5007960100784777511450277 938992518897145783396927)
        ·
          refine ⟨1408488778345718675095391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 938992518897145783396927 1408488778345718675095391)
          ·
            refine ⟨2112733167518578012643087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1408488778345718675095391 2112733167518578012643087)
            ·
              refine ⟨3169099751277867018964631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2112733167518578012643087 3169099751277867018964631)
              ·
                refine ⟨4753649626916800528446947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3169099751277867018964631 4753649626916800528446947)
                ·
                  refine ⟨7130474440375200792670421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4753649626916800528446947 7130474440375200792670421)
                  ·
                    refine ⟨167120494696293768578213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7130474440375200792670421 167120494696293768578213)
                    ·
                      rfl

theorem cell22_488199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_488199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_488199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_488199 prefixEnd_488199 := by exact prefixLift 488199
  have htrace : WordTrace (prefixWord ++ tailWord_488199) baseStart_488199 baseEnd_488199 := by
    simpa [prefixWord, tailWord_488199, baseEnd_488199] using wordTrace_append hprefix tailTrace_488199
  have hstable : (prefixWord ++ tailWord_488199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488199).length < 2 ^ (prefixWord ++ tailWord_488199).sum := by decide
  have hdescent : baseEnd_488199 < baseStart_488199 := by decide
  rcases family_descends (prefixWord ++ tailWord_488199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488274 : List Nat := [3, 2, 2, 1, 1, 2, 3, 8]
def baseStart_488274 : Nat := 118140960795 + 488274 * 2 ^ 59
def prefixEnd_488274 : Nat := 4983230072969 + 3 ^ 40 * 488274 * 2
def baseEnd_488274 : Nat := 18571796525446508105887

theorem tailTrace_488274 : CollatzResearch.WordTrace tailWord_488274 prefixEnd_488274 18571796525446508105887 := by
  unfold tailWord_488274
  simp only [CollatzResearch.WordTrace]
  refine ⟨4452203958268540851311969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11872543888716108936831917 4452203958268540851311969)
  ·
    refine ⟨3339152968701405638483977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4452203958268540851311969 3339152968701405638483977)
    ·
      refine ⟨2504364726526054228862983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3339152968701405638483977 2504364726526054228862983)
      ·
        refine ⟨3756547089789081343294475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2504364726526054228862983 3756547089789081343294475)
        ·
          refine ⟨5634820634683622014941713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3756547089789081343294475 5634820634683622014941713)
          ·
            refine ⟨4226115476012716511206285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5634820634683622014941713 4226115476012716511206285)
            ·
              refine ⟨1584793303504768691702357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4226115476012716511206285 1584793303504768691702357)
              ·
                refine ⟨18571796525446508105887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1584793303504768691702357 18571796525446508105887)
                ·
                  rfl

theorem cell22_488274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 8].length) (baseStart_488274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_488274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_488274 prefixEnd_488274 := by exact prefixLift 488274
  have htrace : WordTrace (prefixWord ++ tailWord_488274) baseStart_488274 baseEnd_488274 := by
    simpa [prefixWord, tailWord_488274, baseEnd_488274] using wordTrace_append hprefix tailTrace_488274
  have hstable : (prefixWord ++ tailWord_488274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488274).length < 2 ^ (prefixWord ++ tailWord_488274).sum := by decide
  have hdescent : baseEnd_488274 < baseStart_488274 := by decide
  rcases family_descends (prefixWord ++ tailWord_488274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488340 : List Nat := [2, 4, 2, 1, 1, 1, 2, 5, 1, 3]
def baseStart_488340 : Nat := 118140960795 + 488340 * 2 ^ 59
def prefixEnd_488340 : Nat := 4983230072969 + 3 ^ 40 * 488340 * 2
def baseEnd_488340 : Nat := 167168761877816400802781

theorem tailTrace_488340 : CollatzResearch.WordTrace tailWord_488340 prefixEnd_488340 167168761877816400802781 := by
  unfold tailWord_488340
  simp only [CollatzResearch.WordTrace]
  refine ⟨8905611525417528338575237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11874148700556704451433649 8905611525417528338575237)
  ·
    refine ⟨1669802161015786563482857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8905611525417528338575237 1669802161015786563482857)
    ·
      refine ⟨1252351620761839922612143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1669802161015786563482857 1252351620761839922612143)
      ·
        refine ⟨1878527431142759883918215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1252351620761839922612143 1878527431142759883918215)
        ·
          refine ⟨2817791146714139825877323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1878527431142759883918215 2817791146714139825877323)
          ·
            refine ⟨4226686720071209738815985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2817791146714139825877323 4226686720071209738815985)
            ·
              refine ⟨3170015040053407304111989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4226686720071209738815985 3170015040053407304111989)
              ·
                refine ⟨297188910005006934760499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3170015040053407304111989 297188910005006934760499)
                ·
                  refine ⟨445783365007510402140749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 297188910005006934760499 445783365007510402140749)
                  ·
                    refine ⟨167168761877816400802781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 445783365007510402140749 167168761877816400802781)
                    ·
                      rfl

theorem cell22_488340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_488340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_488340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_488340 prefixEnd_488340 := by exact prefixLift 488340
  have htrace : WordTrace (prefixWord ++ tailWord_488340) baseStart_488340 baseEnd_488340 := by
    simpa [prefixWord, tailWord_488340, baseEnd_488340] using wordTrace_append hprefix tailTrace_488340
  have hstable : (prefixWord ++ tailWord_488340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488340).length < 2 ^ (prefixWord ++ tailWord_488340).sum := by decide
  have hdescent : baseEnd_488340 < baseStart_488340 := by decide
  rcases family_descends (prefixWord ++ tailWord_488340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488353 : List Nat := [1, 2, 3, 4, 1, 2, 2, 2, 5]
def baseStart_488353 : Nat := 118140960795 + 488353 * 2 ^ 59
def prefixEnd_488353 : Nat := 4983230072969 + 3 ^ 40 * 488353 * 2
def baseEnd_488353 : Nat := 55724404014496233409247

theorem tailTrace_488353 : CollatzResearch.WordTrace tailWord_488353 prefixEnd_488353 55724404014496233409247 := by
  unfold tailWord_488353
  simp only [CollatzResearch.WordTrace]
  refine ⟨17811697199787959897373713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11874464799858639931582475 17811697199787959897373713)
  ·
    refine ⟨13358772899840969923030285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17811697199787959897373713 13358772899840969923030285)
    ·
      refine ⟨5009539837440363721136357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13358772899840969923030285 5009539837440363721136357)
      ·
        refine ⟨939288719520068197713067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5009539837440363721136357 939288719520068197713067)
        ·
          refine ⟨1408933079280102296569601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 939288719520068197713067 1408933079280102296569601)
          ·
            refine ⟨1056699809460076722427201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1408933079280102296569601 1056699809460076722427201)
            ·
              refine ⟨792524857095057541820401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1056699809460076722427201 792524857095057541820401)
              ·
                refine ⟨594393642821293156365301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 792524857095057541820401 594393642821293156365301)
                ·
                  refine ⟨55724404014496233409247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 594393642821293156365301 55724404014496233409247)
                  ·
                    rfl

theorem cell22_488353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 2, 5].length) (baseStart_488353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_488353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_488353 prefixEnd_488353 := by exact prefixLift 488353
  have htrace : WordTrace (prefixWord ++ tailWord_488353) baseStart_488353 baseEnd_488353 := by
    simpa [prefixWord, tailWord_488353, baseEnd_488353] using wordTrace_append hprefix tailTrace_488353
  have hstable : (prefixWord ++ tailWord_488353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488353).length < 2 ^ (prefixWord ++ tailWord_488353).sum := by decide
  have hdescent : baseEnd_488353 < baseStart_488353 := by decide
  rcases family_descends (prefixWord ++ tailWord_488353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488374 : List Nat := [5, 1, 4, 1, 1, 1, 1, 2, 3, 3]
def baseStart_488374 : Nat := 118140960795 + 488374 * 2 ^ 59
def prefixEnd_488374 : Nat := 4983230072969 + 3 ^ 40 * 488374 * 2
def baseEnd_488374 : Nat := 167180400772651645452677

theorem tailTrace_488374 : CollatzResearch.WordTrace tailWord_488374 prefixEnd_488374 167180400772651645452677 := by
  unfold tailWord_488374
  simp only [CollatzResearch.WordTrace]
  refine ⟨1113278945794492530243011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11874975421807920322592117 1113278945794492530243011)
  ·
    refine ⟨1669918418691738795364517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1113278945794492530243011 1669918418691738795364517)
    ·
      refine ⟨313109703504701024130847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1669918418691738795364517 313109703504701024130847)
      ·
        refine ⟨469664555257051536196271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313109703504701024130847 469664555257051536196271)
        ·
          refine ⟨704496832885577304294407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469664555257051536196271 704496832885577304294407)
          ·
            refine ⟨1056745249328365956441611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 704496832885577304294407 1056745249328365956441611)
            ·
              refine ⟨1585117873992548934662417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1056745249328365956441611 1585117873992548934662417)
              ·
                refine ⟨1188838405494411700996813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1585117873992548934662417 1188838405494411700996813)
                ·
                  refine ⟨445814402060404387873805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1188838405494411700996813 445814402060404387873805)
                  ·
                    refine ⟨167180400772651645452677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 445814402060404387873805 167180400772651645452677)
                    ·
                      rfl

theorem cell22_488374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_488374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_488374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_488374 prefixEnd_488374 := by exact prefixLift 488374
  have htrace : WordTrace (prefixWord ++ tailWord_488374) baseStart_488374 baseEnd_488374 := by
    simpa [prefixWord, tailWord_488374, baseEnd_488374] using wordTrace_append hprefix tailTrace_488374
  have hstable : (prefixWord ++ tailWord_488374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488374).length < 2 ^ (prefixWord ++ tailWord_488374).sum := by decide
  have hdescent : baseEnd_488374 < baseStart_488374 := by decide
  rcases family_descends (prefixWord ++ tailWord_488374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488396 : List Nat := [2, 2, 1, 4, 1, 1, 1, 4, 1, 5]
def baseStart_488396 : Nat := 118140960795 + 488396 * 2 ^ 59
def prefixEnd_488396 : Nat := 4983230072969 + 3 ^ 40 * 488396 * 2
def baseEnd_488396 : Nat := 167187931822250921402609

theorem tailTrace_488396 : CollatzResearch.WordTrace tailWord_488396 prefixEnd_488396 167187931822250921402609 := by
  unfold tailWord_488396
  simp only [CollatzResearch.WordTrace]
  refine ⟨8906632769316089120594521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11875510359088118827459361 8906632769316089120594521)
  ·
    refine ⟨6679974576987066840445891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8906632769316089120594521 6679974576987066840445891)
    ·
      refine ⟨10019961865480600260668837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6679974576987066840445891 10019961865480600260668837)
      ·
        refine ⟨1878742849777612548875407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10019961865480600260668837 1878742849777612548875407)
        ·
          refine ⟨2818114274666418823313111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1878742849777612548875407 2818114274666418823313111)
          ·
            refine ⟨4227171411999628234969667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2818114274666418823313111 4227171411999628234969667)
            ·
              refine ⟨6340757117999442352454501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4227171411999628234969667 6340757117999442352454501)
              ·
                refine ⟨1188891959624895441085219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6340757117999442352454501 1188891959624895441085219)
                ·
                  refine ⟨1783337939437343161627829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1188891959624895441085219 1783337939437343161627829)
                  ·
                    refine ⟨167187931822250921402609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1783337939437343161627829 167187931822250921402609)
                    ·
                      rfl

theorem cell22_488396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 4, 1, 5].length) (baseStart_488396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_488396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_488396 prefixEnd_488396 := by exact prefixLift 488396
  have htrace : WordTrace (prefixWord ++ tailWord_488396) baseStart_488396 baseEnd_488396 := by
    simpa [prefixWord, tailWord_488396, baseEnd_488396] using wordTrace_append hprefix tailTrace_488396
  have hstable : (prefixWord ++ tailWord_488396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488396).length < 2 ^ (prefixWord ++ tailWord_488396).sum := by decide
  have hdescent : baseEnd_488396 < baseStart_488396 := by decide
  rcases family_descends (prefixWord ++ tailWord_488396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488398 : List Nat := [4, 1, 1, 1, 2, 3, 1, 5, 4]
def baseStart_488398 : Nat := 118140960795 + 488398 * 2 ^ 59
def prefixEnd_488398 : Nat := 4983230072969 + 3 ^ 40 * 488398 * 2
def baseEnd_488398 : Nat := 55729538821041194284201

theorem tailTrace_488398 : CollatzResearch.WordTrace tailWord_488398 prefixEnd_488398 55729538821041194284201 := by
  unfold tailWord_488398
  simp only [CollatzResearch.WordTrace]
  refine ⟨2226667310578116572845231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11875558989749955055174565 2226667310578116572845231)
  ·
    refine ⟨3340000965867174859267847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2226667310578116572845231 3340000965867174859267847)
    ·
      refine ⟨5010001448800762288901771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3340000965867174859267847 5010001448800762288901771)
      ·
        refine ⟨7515002173201143433352657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5010001448800762288901771 7515002173201143433352657)
        ·
          refine ⟨5636251629900857575014493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7515002173201143433352657 5636251629900857575014493)
          ·
            refine ⟨2113594361212821590630435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5636251629900857575014493 2113594361212821590630435)
            ·
              refine ⟨3170391541819232385945653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2113594361212821590630435 3170391541819232385945653)
              ·
                refine ⟨297224207045553036182405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3170391541819232385945653 297224207045553036182405)
                ·
                  refine ⟨55729538821041194284201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 297224207045553036182405 55729538821041194284201)
                  ·
                    rfl

theorem cell22_488398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 5, 4].length) (baseStart_488398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_488398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_488398 prefixEnd_488398 := by exact prefixLift 488398
  have htrace : WordTrace (prefixWord ++ tailWord_488398) baseStart_488398 baseEnd_488398 := by
    simpa [prefixWord, tailWord_488398, baseEnd_488398] using wordTrace_append hprefix tailTrace_488398
  have hstable : (prefixWord ++ tailWord_488398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488398).length < 2 ^ (prefixWord ++ tailWord_488398).sum := by decide
  have hdescent : baseEnd_488398 < baseStart_488398 := by decide
  rcases family_descends (prefixWord ++ tailWord_488398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488430 : List Nat := [4, 1, 2, 1, 4, 2, 1, 1, 1, 5]
def baseStart_488430 : Nat := 118140960795 + 488430 * 2 ^ 59
def prefixEnd_488430 : Nat := 4983230072969 + 3 ^ 40 * 488430 * 2
def baseEnd_488430 : Nat := 167199570717086166052505

theorem tailTrace_488430 : CollatzResearch.WordTrace tailWord_488430 prefixEnd_488430 167199570717086166052505 := by
  unfold tailWord_488430
  simp only [CollatzResearch.WordTrace]
  refine ⟨2226813202563625255990843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11876337080339334698617829 2226813202563625255990843)
  ·
    refine ⟨3340219803845437883986265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2226813202563625255990843 3340219803845437883986265)
    ·
      refine ⟨2505164852884078412989699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3340219803845437883986265 2505164852884078412989699)
      ·
        refine ⟨3757747279326117619484549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2505164852884078412989699 3757747279326117619484549)
        ·
          refine ⟨704577614873647053653353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3757747279326117619484549 704577614873647053653353)
          ·
            refine ⟨528433211155235290240015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 704577614873647053653353 528433211155235290240015)
            ·
              refine ⟨792649816732852935360023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 528433211155235290240015 792649816732852935360023)
              ·
                refine ⟨1188974725099279403040035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 792649816732852935360023 1188974725099279403040035)
                ·
                  refine ⟨1783462087648919104560053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1188974725099279403040035 1783462087648919104560053)
                  ·
                    refine ⟨167199570717086166052505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1783462087648919104560053 167199570717086166052505)
                    ·
                      rfl

theorem cell22_488430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_488430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_488430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_488430 prefixEnd_488430 := by exact prefixLift 488430
  have htrace : WordTrace (prefixWord ++ tailWord_488430) baseStart_488430 baseEnd_488430 := by
    simpa [prefixWord, tailWord_488430, baseEnd_488430] using wordTrace_append hprefix tailTrace_488430
  have hstable : (prefixWord ++ tailWord_488430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488430).length < 2 ^ (prefixWord ++ tailWord_488430).sum := by decide
  have hdescent : baseEnd_488430 < baseStart_488430 := by decide
  rcases family_descends (prefixWord ++ tailWord_488430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488466 : List Nat := [3, 2, 5, 1, 1, 1, 3, 2, 4]
def baseStart_488466 : Nat := 118140960795 + 488466 * 2 ^ 59
def prefixEnd_488466 : Nat := 4983230072969 + 3 ^ 40 * 488466 * 2
def baseEnd_488466 : Nat := 55737298084264690717465

theorem tailTrace_488466 : CollatzResearch.WordTrace tailWord_488466 prefixEnd_488466 55737298084264690717465 := by
  unfold tailWord_488466
  simp only [CollatzResearch.WordTrace]
  refine ⟨4453954662094645049059313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11877212432252386797491501 4453954662094645049059313)
  ·
    refine ⟨3340465996570983786794485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4453954662094645049059313 3340465996570983786794485)
    ·
      refine ⟨313168687178529730011983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3340465996570983786794485 313168687178529730011983)
      ·
        refine ⟨469753030767794595017975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313168687178529730011983 469753030767794595017975)
        ·
          refine ⟨704629546151691892526963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469753030767794595017975 704629546151691892526963)
          ·
            refine ⟨1056944319227537838790445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 704629546151691892526963 1056944319227537838790445)
            ·
              refine ⟨396354119710326689546417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1056944319227537838790445 396354119710326689546417)
              ·
                refine ⟨297265589782745017159813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 396354119710326689546417 297265589782745017159813)
                ·
                  refine ⟨55737298084264690717465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 297265589782745017159813 55737298084264690717465)
                  ·
                    rfl

theorem cell22_488466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 3, 2, 4].length) (baseStart_488466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_488466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_488466 prefixEnd_488466 := by exact prefixLift 488466
  have htrace : WordTrace (prefixWord ++ tailWord_488466) baseStart_488466 baseEnd_488466 := by
    simpa [prefixWord, tailWord_488466, baseEnd_488466] using wordTrace_append hprefix tailTrace_488466
  have hstable : (prefixWord ++ tailWord_488466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488466).length < 2 ^ (prefixWord ++ tailWord_488466).sum := by decide
  have hdescent : baseEnd_488466 < baseStart_488466 := by decide
  rcases family_descends (prefixWord ++ tailWord_488466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488548 : List Nat := [2, 3, 1, 1, 2, 1, 1, 2, 6, 3]
def baseStart_488548 : Nat := 118140960795 + 488548 * 2 ^ 59
def prefixEnd_488548 : Nat := 4983230072969 + 3 ^ 40 * 488548 * 2
def baseEnd_488548 : Nat := 167239964528573191602143

theorem tailTrace_488548 : CollatzResearch.WordTrace tailWord_488548 prefixEnd_488548 167239964528573191602143 := by
  unfold tailWord_488548
  simp only [CollatzResearch.WordTrace]
  refine ⟨8909404717040754100361149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11879206289387672133814865 8909404717040754100361149)
  ·
    refine ⟨3341026768890282787635431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8909404717040754100361149 3341026768890282787635431)
    ·
      refine ⟨5011540153335424181453147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3341026768890282787635431 5011540153335424181453147)
      ·
        refine ⟨7517310230003136272179721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5011540153335424181453147 7517310230003136272179721)
        ·
          refine ⟨5637982672502352204134791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7517310230003136272179721 5637982672502352204134791)
          ·
            refine ⟨8456974008753528306202187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5637982672502352204134791 8456974008753528306202187)
            ·
              refine ⟨12685461013130292459303281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8456974008753528306202187 12685461013130292459303281)
              ·
                refine ⟨9514095759847719344477461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12685461013130292459303281 9514095759847719344477461)
                ·
                  refine ⟨445973238742861844272381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9514095759847719344477461 445973238742861844272381)
                  ·
                    refine ⟨167239964528573191602143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 445973238742861844272381 167239964528573191602143)
                    ·
                      rfl

theorem cell22_488548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 6, 3].length) (baseStart_488548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_488548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_488548 prefixEnd_488548 := by exact prefixLift 488548
  have htrace : WordTrace (prefixWord ++ tailWord_488548) baseStart_488548 baseEnd_488548 := by
    simpa [prefixWord, tailWord_488548, baseEnd_488548] using wordTrace_append hprefix tailTrace_488548
  have hstable : (prefixWord ++ tailWord_488548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488548).length < 2 ^ (prefixWord ++ tailWord_488548).sum := by decide
  have hdescent : baseEnd_488548 < baseStart_488548 := by decide
  rcases family_descends (prefixWord ++ tailWord_488548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488569 : List Nat := [1, 2, 1, 3, 6, 1, 2, 1, 1, 4]
def baseStart_488569 : Nat := 118140960795 + 488569 * 2 ^ 59
def prefixEnd_488569 : Nat := 4983230072969 + 3 ^ 40 * 488569 * 2
def baseEnd_488569 : Nat := 167247153257736136827079

theorem tailTrace_488569 : CollatzResearch.WordTrace tailWord_488569 prefixEnd_488569 167247153257736136827079 := by
  unfold tailWord_488569
  simp only [CollatzResearch.WordTrace]
  refine ⟨17819575367005428787236761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11879716911336952524824507 17819575367005428787236761)
  ·
    refine ⟨13364681525254071590427571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17819575367005428787236761 13364681525254071590427571)
    ·
      refine ⟨20047022287881107385641357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13364681525254071590427571 20047022287881107385641357)
      ·
        refine ⟨7517633357955415269615509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20047022287881107385641357 7517633357955415269615509)
        ·
          refine ⟨352389063654160090763227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7517633357955415269615509 352389063654160090763227)
          ·
            refine ⟨528583595481240136144841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352389063654160090763227 528583595481240136144841)
            ·
              refine ⟨396437696610930102108631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 528583595481240136144841 396437696610930102108631)
              ·
                refine ⟨594656544916395153162947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 396437696610930102108631 594656544916395153162947)
                ·
                  refine ⟨891984817374592729744421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 594656544916395153162947 891984817374592729744421)
                  ·
                    refine ⟨167247153257736136827079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 891984817374592729744421 167247153257736136827079)
                    ·
                      rfl

theorem cell22_488569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 2, 1, 1, 4].length) (baseStart_488569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_488569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_488569 prefixEnd_488569 := by exact prefixLift 488569
  have htrace : WordTrace (prefixWord ++ tailWord_488569) baseStart_488569 baseEnd_488569 := by
    simpa [prefixWord, tailWord_488569, baseEnd_488569] using wordTrace_append hprefix tailTrace_488569
  have hstable : (prefixWord ++ tailWord_488569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488569).length < 2 ^ (prefixWord ++ tailWord_488569).sum := by decide
  have hdescent : baseEnd_488569 < baseStart_488569 := by decide
  rcases family_descends (prefixWord ++ tailWord_488569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488591 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 6, 6]
def baseStart_488591 : Nat := 118140960795 + 488591 * 2 ^ 59
def prefixEnd_488591 : Nat := 4983230072969 + 3 ^ 40 * 488591 * 2
def baseEnd_488591 : Nat := 167254684307335412777011

theorem tailTrace_488591 : CollatzResearch.WordTrace tailWord_488591 prefixEnd_488591 167254684307335412777011 := by
  unfold tailWord_488591
  simp only [CollatzResearch.WordTrace]
  refine ⟨17820377772925726544537627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11880251848617151029691751 17820377772925726544537627)
  ·
    refine ⟨26730566659388589816806441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17820377772925726544537627 26730566659388589816806441)
    ·
      refine ⟨20047924994541442362604831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26730566659388589816806441 20047924994541442362604831)
      ·
        refine ⟨30071887491812163543907247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20047924994541442362604831 30071887491812163543907247)
        ·
          refine ⟨45107831237718245315860871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30071887491812163543907247 45107831237718245315860871)
          ·
            refine ⟨67661746856577367973791307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45107831237718245315860871 67661746856577367973791307)
            ·
              refine ⟨101492620284866051960686961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67661746856577367973791307 101492620284866051960686961)
              ·
                refine ⟨76119465213649538970515221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101492620284866051960686961 76119465213649538970515221)
                ·
                  refine ⟨3568099931889822139242901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 76119465213649538970515221 3568099931889822139242901)
                  ·
                    refine ⟨167254684307335412777011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3568099931889822139242901 167254684307335412777011)
                    ·
                      rfl

theorem cell22_488591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 6].length) (baseStart_488591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_488591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_488591 prefixEnd_488591 := by exact prefixLift 488591
  have htrace : WordTrace (prefixWord ++ tailWord_488591) baseStart_488591 baseEnd_488591 := by
    simpa [prefixWord, tailWord_488591, baseEnd_488591] using wordTrace_append hprefix tailTrace_488591
  have hstable : (prefixWord ++ tailWord_488591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488591).length < 2 ^ (prefixWord ++ tailWord_488591).sum := by decide
  have hdescent : baseEnd_488591 < baseStart_488591 := by decide
  rcases family_descends (prefixWord ++ tailWord_488591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488627 : List Nat := [1, 1, 1, 2, 3, 2, 5, 3, 1, 3]
def baseStart_488627 : Nat := 118140960795 + 488627 * 2 ^ 59
def prefixEnd_488627 : Nat := 4983230072969 + 3 ^ 40 * 488627 * 2
def baseEnd_488627 : Nat := 167267007843043318876901

theorem tailTrace_488627 : CollatzResearch.WordTrace tailWord_488627 prefixEnd_488627 167267007843043318876901 := by
  unfold tailWord_488627
  simp only [CollatzResearch.WordTrace]
  refine ⟨17821690800795304692848135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11881127200530203128565423 17821690800795304692848135)
  ·
    refine ⟨26732536201192957039272203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17821690800795304692848135 26732536201192957039272203)
    ·
      refine ⟨40098804301789435558908305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26732536201192957039272203 40098804301789435558908305)
      ·
        refine ⟨30074103226342076669181229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40098804301789435558908305 30074103226342076669181229)
        ·
          refine ⟨11277788709878278750942961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30074103226342076669181229 11277788709878278750942961)
          ·
            refine ⟨8458341532408709063207221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11277788709878278750942961 8458341532408709063207221)
            ·
              refine ⟨792969518663316474675677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8458341532408709063207221 792969518663316474675677)
              ·
                refine ⟨297363569498743678003379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 792969518663316474675677 297363569498743678003379)
                ·
                  refine ⟨446045354248115517005069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 297363569498743678003379 446045354248115517005069)
                  ·
                    refine ⟨167267007843043318876901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 446045354248115517005069 167267007843043318876901)
                    ·
                      rfl

theorem cell22_488627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 3, 1, 3].length) (baseStart_488627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_488627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_488627 prefixEnd_488627 := by exact prefixLift 488627
  have htrace : WordTrace (prefixWord ++ tailWord_488627) baseStart_488627 baseEnd_488627 := by
    simpa [prefixWord, tailWord_488627, baseEnd_488627] using wordTrace_append hprefix tailTrace_488627
  have hstable : (prefixWord ++ tailWord_488627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488627).length < 2 ^ (prefixWord ++ tailWord_488627).sum := by decide
  have hdescent : baseEnd_488627 < baseStart_488627 := by decide
  rcases family_descends (prefixWord ++ tailWord_488627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488644 : List Nat := [2, 3, 3, 1, 3, 2, 1, 1, 3, 3]
def baseStart_488644 : Nat := 118140960795 + 488644 * 2 ^ 59
def prefixEnd_488644 : Nat := 4983230072969 + 3 ^ 40 * 488644 * 2
def baseEnd_488644 : Nat := 167272827290460941201849

theorem tailTrace_488644 : CollatzResearch.WordTrace tailWord_488644 prefixEnd_488644 167272827290460941201849 := by
  unfold tailWord_488644
  simp only [CollatzResearch.WordTrace]
  refine ⟨8911155420866858298108493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11881540561155811064144657 8911155420866858298108493)
  ·
    refine ⟨3341683282825071861790685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8911155420866858298108493 3341683282825071861790685)
    ·
      refine ⟨1253131231059401948171507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3341683282825071861790685 1253131231059401948171507)
      ·
        refine ⟨1879696846589102922257261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1253131231059401948171507 1879696846589102922257261)
        ·
          refine ⟨704886317470913595846473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1879696846589102922257261 704886317470913595846473)
          ·
            refine ⟨528664738103185196884855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 704886317470913595846473 528664738103185196884855)
            ·
              refine ⟨792997107154777795327283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 528664738103185196884855 792997107154777795327283)
              ·
                refine ⟨1189495660732166692990925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 792997107154777795327283 1189495660732166692990925)
                ·
                  refine ⟨446060872774562509871597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1189495660732166692990925 446060872774562509871597)
                  ·
                    refine ⟨167272827290460941201849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 446060872774562509871597 167272827290460941201849)
                    ·
                      rfl

theorem cell22_488644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_488644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_488644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_488644 prefixEnd_488644 := by exact prefixLift 488644
  have htrace : WordTrace (prefixWord ++ tailWord_488644) baseStart_488644 baseEnd_488644 := by
    simpa [prefixWord, tailWord_488644, baseEnd_488644] using wordTrace_append hprefix tailTrace_488644
  have hstable : (prefixWord ++ tailWord_488644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488644).length < 2 ^ (prefixWord ++ tailWord_488644).sum := by decide
  have hdescent : baseEnd_488644 < baseStart_488644 := by decide
  rcases family_descends (prefixWord ++ tailWord_488644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488683 : List Nat := [1, 1, 1, 1, 2, 6, 1, 1, 3, 5]
def baseStart_488683 : Nat := 118140960795 + 488683 * 2 ^ 59
def prefixEnd_488683 : Nat := 4983230072969 + 3 ^ 40 * 488683 * 2
def baseEnd_488683 : Nat := 167286177787477839476729

theorem tailTrace_488683 : CollatzResearch.WordTrace tailWord_488683 prefixEnd_488683 167286177787477839476729 := by
  unfold tailWord_488683
  simp only [CollatzResearch.WordTrace]
  refine ⟨17823733288592426256886703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11882488859061617504591135 17823733288592426256886703)
  ·
    refine ⟨26735599932888639385330055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17823733288592426256886703 26735599932888639385330055)
    ·
      refine ⟨40103399899332959077995083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26735599932888639385330055 40103399899332959077995083)
      ·
        refine ⟨60155099848999438616992625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40103399899332959077995083 60155099848999438616992625)
        ·
          refine ⟨45116324886749578962744469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60155099848999438616992625 45116324886749578962744469)
          ·
            refine ⟨2114827729066386513878647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 45116324886749578962744469 2114827729066386513878647)
            ·
              refine ⟨3172241593599579770817971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2114827729066386513878647 3172241593599579770817971)
              ·
                refine ⟨4758362390399369656226957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3172241593599579770817971 4758362390399369656226957)
                ·
                  refine ⟨1784385896399763621085109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4758362390399369656226957 1784385896399763621085109)
                  ·
                    refine ⟨167286177787477839476729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1784385896399763621085109 167286177787477839476729)
                    ·
                      rfl

theorem cell22_488683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 3, 5].length) (baseStart_488683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_488683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_488683 prefixEnd_488683 := by exact prefixLift 488683
  have htrace : WordTrace (prefixWord ++ tailWord_488683) baseStart_488683 baseEnd_488683 := by
    simpa [prefixWord, tailWord_488683, baseEnd_488683] using wordTrace_append hprefix tailTrace_488683
  have hstable : (prefixWord ++ tailWord_488683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488683).length < 2 ^ (prefixWord ++ tailWord_488683).sum := by decide
  have hdescent : baseEnd_488683 < baseStart_488683 := by decide
  rcases family_descends (prefixWord ++ tailWord_488683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488762 : List Nat := [3, 1, 1, 1, 4, 1, 4, 1, 3, 3]
def baseStart_488762 : Nat := 118140960795 + 488762 * 2 ^ 59
def prefixEnd_488762 : Nat := 4983230072969 + 3 ^ 40 * 488762 * 2
def baseEnd_488762 : Nat := 167313221101947966751487

theorem tailTrace_488762 : CollatzResearch.WordTrace tailWord_488762 prefixEnd_488762 167313221101947966751487 := by
  unfold tailWord_488762
  simp only [CollatzResearch.WordTrace]
  refine ⟨4456653663826555687253135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11884409770204148499341693 4456653663826555687253135)
  ·
    refine ⟨6684980495739833530879703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4456653663826555687253135 6684980495739833530879703)
    ·
      refine ⟨10027470743609750296319555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6684980495739833530879703 10027470743609750296319555)
      ·
        refine ⟨15041206115414625444479333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10027470743609750296319555 15041206115414625444479333)
        ·
          refine ⟨2820226146640242270839875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15041206115414625444479333 2820226146640242270839875)
          ·
            refine ⟨4230339219960363406259813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2820226146640242270839875 4230339219960363406259813)
            ·
              refine ⟨793188603742568138673715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4230339219960363406259813 793188603742568138673715)
              ·
                refine ⟨1189782905613852208010573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 793188603742568138673715 1189782905613852208010573)
                ·
                  refine ⟨446168589605194578003965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1189782905613852208010573 446168589605194578003965)
                  ·
                    refine ⟨167313221101947966751487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 446168589605194578003965 167313221101947966751487)
                    ·
                      rfl

theorem cell22_488762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 1, 3, 3].length) (baseStart_488762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_488762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_488762 prefixEnd_488762 := by exact prefixLift 488762
  have htrace : WordTrace (prefixWord ++ tailWord_488762) baseStart_488762 baseEnd_488762 := by
    simpa [prefixWord, tailWord_488762, baseEnd_488762] using wordTrace_append hprefix tailTrace_488762
  have hstable : (prefixWord ++ tailWord_488762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488762).length < 2 ^ (prefixWord ++ tailWord_488762).sum := by decide
  have hdescent : baseEnd_488762 < baseStart_488762 := by decide
  rcases family_descends (prefixWord ++ tailWord_488762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488781 : List Nat := [1, 6, 1, 3, 1, 2, 2, 6]
def baseStart_488781 : Nat := 118140960795 + 488781 * 2 ^ 59
def prefixEnd_488781 : Nat := 4983230072969 + 3 ^ 40 * 488781 * 2
def baseEnd_488781 : Nat := 18591080576693138947381

theorem tailTrace_488781 : CollatzResearch.WordTrace tailWord_488781 prefixEnd_488781 18591080576693138947381 := by
  unfold tailWord_488781
  simp only [CollatzResearch.WordTrace]
  refine ⟨17827307642237388993954197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11884871761491592662636131 17827307642237388993954197)
  ·
    refine ⟨835655045729877609091603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17827307642237388993954197 835655045729877609091603)
    ·
      refine ⟨1253482568594816413637405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 835655045729877609091603 1253482568594816413637405)
      ·
        refine ⟨470055963223056155114027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1253482568594816413637405 470055963223056155114027)
        ·
          refine ⟨705083944834584232671041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470055963223056155114027 705083944834584232671041)
          ·
            refine ⟨528812958625938174503281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 705083944834584232671041 528812958625938174503281)
            ·
              refine ⟨396609718969453630877461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 528812958625938174503281 396609718969453630877461)
              ·
                refine ⟨18591080576693138947381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 396609718969453630877461 18591080576693138947381)
                ·
                  rfl

theorem cell22_488781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 2, 6].length) (baseStart_488781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_488781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_488781 prefixEnd_488781 := by exact prefixLift 488781
  have htrace : WordTrace (prefixWord ++ tailWord_488781) baseStart_488781 baseEnd_488781 := by
    simpa [prefixWord, tailWord_488781, baseEnd_488781] using wordTrace_append hprefix tailTrace_488781
  have hstable : (prefixWord ++ tailWord_488781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488781).length < 2 ^ (prefixWord ++ tailWord_488781).sum := by decide
  have hdescent : baseEnd_488781 < baseStart_488781 := by decide
  rcases family_descends (prefixWord ++ tailWord_488781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488839 : List Nat := [1, 1, 4, 2, 2, 4, 1, 2, 1, 4]
def baseStart_488839 : Nat := 118140960795 + 488839 * 2 ^ 59
def prefixEnd_488839 : Nat := 4983230072969 + 3 ^ 40 * 488839 * 2
def baseEnd_488839 : Nat := 167339579775545432576251

theorem tailTrace_488839 : CollatzResearch.WordTrace tailWord_488839 prefixEnd_488839 167339579775545432576251 := by
  unfold tailWord_488839
  simp only [CollatzResearch.WordTrace]
  refine ⟨17829423076027264899565571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11886282050684843266377047 17829423076027264899565571)
  ·
    refine ⟨26744134614040897349348357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17829423076027264899565571 26744134614040897349348357)
    ·
      refine ⟨5014525240132668253002817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26744134614040897349348357 5014525240132668253002817)
      ·
        refine ⟨3760893930099501189752113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5014525240132668253002817 3760893930099501189752113)
        ·
          refine ⟨2820670447574625892314085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3760893930099501189752113 2820670447574625892314085)
          ·
            refine ⟨528875708920242354808891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2820670447574625892314085 528875708920242354808891)
            ·
              refine ⟨793313563380363532213337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 528875708920242354808891 793313563380363532213337)
              ·
                refine ⟨594985172535272649160003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 793313563380363532213337 594985172535272649160003)
                ·
                  refine ⟨892477758802908973740005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 594985172535272649160003 892477758802908973740005)
                  ·
                    refine ⟨167339579775545432576251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 892477758802908973740005 167339579775545432576251)
                    ·
                      rfl

theorem cell22_488839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 2, 1, 4].length) (baseStart_488839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_488839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_488839 prefixEnd_488839 := by exact prefixLift 488839
  have htrace : WordTrace (prefixWord ++ tailWord_488839) baseStart_488839 baseEnd_488839 := by
    simpa [prefixWord, tailWord_488839, baseEnd_488839] using wordTrace_append hprefix tailTrace_488839
  have hstable : (prefixWord ++ tailWord_488839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488839).length < 2 ^ (prefixWord ++ tailWord_488839).sum := by decide
  have hdescent : baseEnd_488839 < baseStart_488839 := by decide
  rcases family_descends (prefixWord ++ tailWord_488839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488852 : List Nat := [2, 4, 2, 1, 2, 1, 1, 1, 3, 5]
def baseStart_488852 : Nat := 118140960795 + 488852 * 2 ^ 59
def prefixEnd_488852 : Nat := 4983230072969 + 3 ^ 40 * 488852 * 2
def baseEnd_488852 : Nat := 167344029941217732001211

theorem tailTrace_488852 : CollatzResearch.WordTrace tailWord_488852 prefixEnd_488852 167344029941217732001211 := by
  unfold tailWord_488852
  simp only [CollatzResearch.WordTrace]
  refine ⟨8914948612490084059894405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11886598149986778746525873 8914948612490084059894405)
  ·
    refine ⟨1671552864841890761230201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8914948612490084059894405 1671552864841890761230201)
    ·
      refine ⟨1253664648631418070922651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1671552864841890761230201 1253664648631418070922651)
      ·
        refine ⟨1880496972947127106383977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1253664648631418070922651 1880496972947127106383977)
        ·
          refine ⟨1410372729710345329787983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1880496972947127106383977 1410372729710345329787983)
          ·
            refine ⟨2115559094565517994681975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1410372729710345329787983 2115559094565517994681975)
            ·
              refine ⟨3173338641848276992022963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2115559094565517994681975 3173338641848276992022963)
              ·
                refine ⟨4760007962772415488034445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3173338641848276992022963 4760007962772415488034445)
                ·
                  refine ⟨1785002986039655808012917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4760007962772415488034445 1785002986039655808012917)
                  ·
                    refine ⟨167344029941217732001211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1785002986039655808012917 167344029941217732001211)
                    ·
                      rfl

theorem cell22_488852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_488852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_488852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_488852 prefixEnd_488852 := by exact prefixLift 488852
  have htrace : WordTrace (prefixWord ++ tailWord_488852) baseStart_488852 baseEnd_488852 := by
    simpa [prefixWord, tailWord_488852, baseEnd_488852] using wordTrace_append hprefix tailTrace_488852
  have hstable : (prefixWord ++ tailWord_488852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488852).length < 2 ^ (prefixWord ++ tailWord_488852).sum := by decide
  have hdescent : baseEnd_488852 < baseStart_488852 := by decide
  rcases family_descends (prefixWord ++ tailWord_488852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488856 : List Nat := [2, 1, 2, 5, 2, 1, 3, 1, 1, 4]
def baseStart_488856 : Nat := 118140960795 + 488856 * 2 ^ 59
def prefixEnd_488856 : Nat := 4983230072969 + 3 ^ 40 * 488856 * 2
def baseEnd_488856 : Nat := 167345399222963054901199

theorem tailTrace_488856 : CollatzResearch.WordTrace tailWord_488856 prefixEnd_488856 167345399222963054901199 := by
  unfold tailWord_488856
  simp only [CollatzResearch.WordTrace]
  refine ⟨8915021558482838401467211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11886695411310451201956281 8915021558482838401467211)
  ·
    refine ⟨13372532337724257602200817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8915021558482838401467211 13372532337724257602200817)
    ·
      refine ⟨10029399253293193201650613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13372532337724257602200817 10029399253293193201650613)
      ·
        refine ⟨940256179996236862654745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10029399253293193201650613 940256179996236862654745)
        ·
          refine ⟨705192134997177646991059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 940256179996236862654745 705192134997177646991059)
          ·
            refine ⟨1057788202495766470486589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 705192134997177646991059 1057788202495766470486589)
            ·
              refine ⟨396670575935912426432471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1057788202495766470486589 396670575935912426432471)
              ·
                refine ⟨595005863903868639648707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 396670575935912426432471 595005863903868639648707)
                ·
                  refine ⟨892508795855802959473061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 595005863903868639648707 892508795855802959473061)
                  ·
                    refine ⟨167345399222963054901199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 892508795855802959473061 167345399222963054901199)
                    ·
                      rfl

theorem cell22_488856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 3, 1, 1, 4].length) (baseStart_488856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_488856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_488856 prefixEnd_488856 := by exact prefixLift 488856
  have htrace : WordTrace (prefixWord ++ tailWord_488856) baseStart_488856 baseEnd_488856 := by
    simpa [prefixWord, tailWord_488856, baseEnd_488856] using wordTrace_append hprefix tailTrace_488856
  have hstable : (prefixWord ++ tailWord_488856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488856).length < 2 ^ (prefixWord ++ tailWord_488856).sum := by decide
  have hdescent : baseEnd_488856 < baseStart_488856 := by decide
  rcases family_descends (prefixWord ++ tailWord_488856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488931 : List Nat := [1, 1, 1, 6, 2, 1, 2, 4, 1, 3]
def baseStart_488931 : Nat := 118140960795 + 488931 * 2 ^ 59
def prefixEnd_488931 : Nat := 4983230072969 + 3 ^ 40 * 488931 * 2
def baseEnd_488931 : Nat := 167371073255687859275969

theorem tailTrace_488931 : CollatzResearch.WordTrace tailWord_488931 prefixEnd_488931 167371073255687859275969 := by
  unfold tailWord_488931
  simp only [CollatzResearch.WordTrace]
  refine ⟨17832778591693964611914647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11888519061129309741276431 17832778591693964611914647)
  ·
    refine ⟨26749167887540946917871971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17832778591693964611914647 26749167887540946917871971)
    ·
      refine ⟨40123751831311420376807957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26749167887540946917871971 40123751831311420376807957)
      ·
        refine ⟨1880800867092722830162873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 40123751831311420376807957 1880800867092722830162873)
        ·
          refine ⟨1410600650319542122622155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1880800867092722830162873 1410600650319542122622155)
          ·
            refine ⟨2115900975479313183933233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1410600650319542122622155 2115900975479313183933233)
            ·
              refine ⟨1586925731609484887949925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2115900975479313183933233 1586925731609484887949925)
              ·
                refine ⟨297548574676778416490611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1586925731609484887949925 297548574676778416490611)
                ·
                  refine ⟨446322862015167624735917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 297548574676778416490611 446322862015167624735917)
                  ·
                    refine ⟨167371073255687859275969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 446322862015167624735917 167371073255687859275969)
                    ·
                      rfl

theorem cell22_488931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 4, 1, 3].length) (baseStart_488931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_488931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_488931 prefixEnd_488931 := by exact prefixLift 488931
  have htrace : WordTrace (prefixWord ++ tailWord_488931) baseStart_488931 baseEnd_488931 := by
    simpa [prefixWord, tailWord_488931, baseEnd_488931] using wordTrace_append hprefix tailTrace_488931
  have hstable : (prefixWord ++ tailWord_488931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488931).length < 2 ^ (prefixWord ++ tailWord_488931).sum := by decide
  have hdescent : baseEnd_488931 < baseStart_488931 := by decide
  rcases family_descends (prefixWord ++ tailWord_488931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488940 : List Nat := [2, 2, 1, 1, 2, 1, 2, 1, 2, 8]
def baseStart_488940 : Nat := 118140960795 + 488940 * 2 ^ 59
def prefixEnd_488940 : Nat := 4983230072969 + 3 ^ 40 * 488940 * 2
def baseEnd_488940 : Nat := 167374154139614835800941

theorem tailTrace_488940 : CollatzResearch.WordTrace tailWord_488940 prefixEnd_488940 167374154139614835800941 := by
  unfold tailWord_488940
  simp only [CollatzResearch.WordTrace]
  refine ⟨8916553424330679574496137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11888737899107572765994849 8916553424330679574496137)
  ·
    refine ⟨6687415068248009680872103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8916553424330679574496137 6687415068248009680872103)
    ·
      refine ⟨10031122602372014521308155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6687415068248009680872103 10031122602372014521308155)
      ·
        refine ⟨15046683903558021781962233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10031122602372014521308155 15046683903558021781962233)
        ·
          refine ⟨11285012927668516336471675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15046683903558021781962233 11285012927668516336471675)
          ·
            refine ⟨16927519391502774504707513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11285012927668516336471675 16927519391502774504707513)
            ·
              refine ⟨12695639543627080878530635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16927519391502774504707513 12695639543627080878530635)
              ·
                refine ⟨19043459315440621317795953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12695639543627080878530635 19043459315440621317795953)
                ·
                  refine ⟨14282594486580465988346965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19043459315440621317795953 14282594486580465988346965)
                  ·
                    refine ⟨167374154139614835800941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 14282594486580465988346965 167374154139614835800941)
                    ·
                      rfl

theorem cell22_488940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 8].length) (baseStart_488940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_488940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_488940 prefixEnd_488940 := by exact prefixLift 488940
  have htrace : WordTrace (prefixWord ++ tailWord_488940) baseStart_488940 baseEnd_488940 := by
    simpa [prefixWord, tailWord_488940, baseEnd_488940] using wordTrace_append hprefix tailTrace_488940
  have hstable : (prefixWord ++ tailWord_488940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488940).length < 2 ^ (prefixWord ++ tailWord_488940).sum := by decide
  have hdescent : baseEnd_488940 < baseStart_488940 := by decide
  rcases family_descends (prefixWord ++ tailWord_488940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488942 : List Nat := [4, 1, 2, 1, 2, 1, 1, 3, 2, 5]
def baseStart_488942 : Nat := 118140960795 + 488942 * 2 ^ 59
def prefixEnd_488942 : Nat := 4983230072969 + 3 ^ 40 * 488942 * 2
def baseEnd_488942 : Nat := 167374838780487497250935

theorem tailTrace_488942 : CollatzResearch.WordTrace tailWord_488942 prefixEnd_488942 167374838780487497250935 := by
  unfold tailWord_488942
  simp only [CollatzResearch.WordTrace]
  refine ⟨2229147474331764186320635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11888786529769408993710053 2229147474331764186320635)
  ·
    refine ⟨3343721211497646279480953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2229147474331764186320635 3343721211497646279480953)
    ·
      refine ⟨2507790908623234709610715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3343721211497646279480953 2507790908623234709610715)
      ·
        refine ⟨3761686362934852064416073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2507790908623234709610715 3761686362934852064416073)
        ·
          refine ⟨2821264772201139048312055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3761686362934852064416073 2821264772201139048312055)
          ·
            refine ⟨4231897158301708572468083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2821264772201139048312055 4231897158301708572468083)
            ·
              refine ⟨6347845737452562858702125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4231897158301708572468083 6347845737452562858702125)
              ·
                refine ⟨2380442151544711072013297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6347845737452562858702125 2380442151544711072013297)
                ·
                  refine ⟨1785331613658533304009973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2380442151544711072013297 1785331613658533304009973)
                  ·
                    refine ⟨167374838780487497250935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1785331613658533304009973 167374838780487497250935)
                    ·
                      rfl

theorem cell22_488942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_488942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_488942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_488942 prefixEnd_488942 := by exact prefixLift 488942
  have htrace : WordTrace (prefixWord ++ tailWord_488942) baseStart_488942 baseEnd_488942 := by
    simpa [prefixWord, tailWord_488942, baseEnd_488942] using wordTrace_append hprefix tailTrace_488942
  have hstable : (prefixWord ++ tailWord_488942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488942).length < 2 ^ (prefixWord ++ tailWord_488942).sum := by decide
  have hdescent : baseEnd_488942 < baseStart_488942 := by decide
  rcases family_descends (prefixWord ++ tailWord_488942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488944 : List Nat := [2, 1, 1, 1, 3, 5, 3, 1, 5]
def baseStart_488944 : Nat := 118140960795 + 488944 * 2 ^ 59
def prefixEnd_488944 : Nat := 4983230072969 + 3 ^ 40 * 488944 * 2
def baseEnd_488944 : Nat := 55791841140453386233643

theorem tailTrace_488944 : CollatzResearch.WordTrace tailWord_488944 prefixEnd_488944 55791841140453386233643 := by
  unfold tailWord_488944
  simp only [CollatzResearch.WordTrace]
  refine ⟨8916626370323433916068943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11888835160431245221425257 8916626370323433916068943)
  ·
    refine ⟨13374939555485150874103415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8916626370323433916068943 13374939555485150874103415)
    ·
      refine ⟨20062409333227726311155123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13374939555485150874103415 20062409333227726311155123)
      ·
        refine ⟨30093613999841589466732685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20062409333227726311155123 30093613999841589466732685)
        ·
          refine ⟨11285105249940596050024757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30093613999841589466732685 11285105249940596050024757)
          ·
            refine ⟨1057978617181930879689821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11285105249940596050024757 1057978617181930879689821)
            ·
              refine ⟨396741981443224079883683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1057978617181930879689821 396741981443224079883683)
              ·
                refine ⟨595112972164836119825525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 396741981443224079883683 595112972164836119825525)
                ·
                  refine ⟨55791841140453386233643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 595112972164836119825525 55791841140453386233643)
                  ·
                    rfl

theorem cell22_488944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 3, 1, 5].length) (baseStart_488944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_488944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_488944 prefixEnd_488944 := by exact prefixLift 488944
  have htrace : WordTrace (prefixWord ++ tailWord_488944) baseStart_488944 baseEnd_488944 := by
    simpa [prefixWord, tailWord_488944, baseEnd_488944] using wordTrace_append hprefix tailTrace_488944
  have hstable : (prefixWord ++ tailWord_488944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488944).length < 2 ^ (prefixWord ++ tailWord_488944).sum := by decide
  have hdescent : baseEnd_488944 < baseStart_488944 := by decide
  rcases family_descends (prefixWord ++ tailWord_488944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489017 : List Nat := [1, 2, 1, 5, 1, 2, 2, 8]
def baseStart_489017 : Nat := 118140960795 + 489017 * 2 ^ 59
def prefixEnd_489017 : Nat := 4983230072969 + 3 ^ 40 * 489017 * 2
def baseEnd_489017 : Nat := 18600056979245811291745

theorem tailTrace_489017 : CollatzResearch.WordTrace tailWord_489017 prefixEnd_489017 18600056979245811291745 := by
  unfold tailWord_489017
  simp only [CollatzResearch.WordTrace]
  refine ⟨17835915269382401299545305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11890610179588267533030203 17835915269382401299545305)
  ·
    refine ⟨13376936452036800974658979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17835915269382401299545305 13376936452036800974658979)
    ·
      refine ⟨20065404678055201461988469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13376936452036800974658979 20065404678055201461988469)
      ·
        refine ⟨1881131688567675137061419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20065404678055201461988469 1881131688567675137061419)
        ·
          refine ⟨2821697532851512705592129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1881131688567675137061419 2821697532851512705592129)
          ·
            refine ⟨2116273149638634529194097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2821697532851512705592129 2116273149638634529194097)
            ·
              refine ⟨1587204862228975896895573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2116273149638634529194097 1587204862228975896895573)
              ·
                refine ⟨18600056979245811291745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1587204862228975896895573 18600056979245811291745)
                ·
                  rfl

theorem cell22_489017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 8].length) (baseStart_489017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_489017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_489017 prefixEnd_489017 := by exact prefixLift 489017
  have htrace : WordTrace (prefixWord ++ tailWord_489017) baseStart_489017 baseEnd_489017 := by
    simpa [prefixWord, tailWord_489017, baseEnd_489017] using wordTrace_append hprefix tailTrace_489017
  have hstable : (prefixWord ++ tailWord_489017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489017).length < 2 ^ (prefixWord ++ tailWord_489017).sum := by decide
  have hdescent : baseEnd_489017 < baseStart_489017 := by decide
  rcases family_descends (prefixWord ++ tailWord_489017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489047 : List Nat := [1, 1, 3, 2, 2, 3, 1, 1, 2, 6]
def baseStart_489047 : Nat := 118140960795 + 489047 * 2 ^ 59
def prefixEnd_489047 : Nat := 4983230072969 + 3 ^ 40 * 489047 * 2
def baseEnd_489047 : Nat := 167410782426302223375613

theorem tailTrace_489047 : CollatzResearch.WordTrace tailWord_489047 prefixEnd_489047 167410782426302223375613 := by
  unfold tailWord_489047
  simp only [CollatzResearch.WordTrace]
  refine ⟨17837009459273716423137395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11891339639515810948758263 17837009459273716423137395)
  ·
    refine ⟨26755514188910574634706093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17837009459273716423137395 26755514188910574634706093)
    ·
      refine ⟨10033317820841465488014785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26755514188910574634706093 10033317820841465488014785)
      ·
        refine ⟨7524988365631099116011089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10033317820841465488014785 7524988365631099116011089)
        ·
          refine ⟨5643741274223324337008317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7524988365631099116011089 5643741274223324337008317)
          ·
            refine ⟨2116402977833746626378119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5643741274223324337008317 2116402977833746626378119)
            ·
              refine ⟨3174604466750619939567179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2116402977833746626378119 3174604466750619939567179)
              ·
                refine ⟨4761906700125929909350769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3174604466750619939567179 4761906700125929909350769)
                ·
                  refine ⟨3571430025094447432013077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4761906700125929909350769 3571430025094447432013077)
                  ·
                    refine ⟨167410782426302223375613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3571430025094447432013077 167410782426302223375613)
                    ·
                      rfl

theorem cell22_489047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 6].length) (baseStart_489047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_489047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_489047 prefixEnd_489047 := by exact prefixLift 489047
  have htrace : WordTrace (prefixWord ++ tailWord_489047) baseStart_489047 baseEnd_489047 := by
    simpa [prefixWord, tailWord_489047, baseEnd_489047] using wordTrace_append hprefix tailTrace_489047
  have hstable : (prefixWord ++ tailWord_489047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489047).length < 2 ^ (prefixWord ++ tailWord_489047).sum := by decide
  have hdescent : baseEnd_489047 < baseStart_489047 := by decide
  rcases family_descends (prefixWord ++ tailWord_489047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489066 : List Nat := [3, 1, 3, 2, 1, 3, 1, 2, 3, 3]
def baseStart_489066 : Nat := 118140960795 + 489066 * 2 ^ 59
def prefixEnd_489066 : Nat := 4983230072969 + 3 ^ 40 * 489066 * 2
def baseEnd_489066 : Nat := 167417286514592507150555

theorem tailTrace_489066 : CollatzResearch.WordTrace tailWord_489066 prefixEnd_489066 167417286514592507150555 := by
  unfold tailWord_489066
  simp only [CollatzResearch.WordTrace]
  refine ⟨4459425611551220667019763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11891801630803255112052701 4459425611551220667019763)
  ·
    refine ⟨6689138417326831000529645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4459425611551220667019763 6689138417326831000529645)
    ·
      refine ⟨2508426906497561625198617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6689138417326831000529645 2508426906497561625198617)
      ·
        refine ⟨1881320179873171218898963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2508426906497561625198617 1881320179873171218898963)
        ·
          refine ⟨2821980269809756828348445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1881320179873171218898963 2821980269809756828348445)
          ·
            refine ⟨1058242601178658810630667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2821980269809756828348445 1058242601178658810630667)
            ·
              refine ⟨1587363901767988215946001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1058242601178658810630667 1587363901767988215946001)
              ·
                refine ⟨1190522926325991161959501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1587363901767988215946001 1190522926325991161959501)
                ·
                  refine ⟨446446097372246685734813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1190522926325991161959501 446446097372246685734813)
                  ·
                    refine ⟨167417286514592507150555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 446446097372246685734813 167417286514592507150555)
                    ·
                      rfl

theorem cell22_489066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_489066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_489066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_489066 prefixEnd_489066 := by exact prefixLift 489066
  have htrace : WordTrace (prefixWord ++ tailWord_489066) baseStart_489066 baseEnd_489066 := by
    simpa [prefixWord, tailWord_489066, baseEnd_489066] using wordTrace_append hprefix tailTrace_489066
  have hstable : (prefixWord ++ tailWord_489066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489066).length < 2 ^ (prefixWord ++ tailWord_489066).sum := by decide
  have hdescent : baseEnd_489066 < baseStart_489066 := by decide
  rcases family_descends (prefixWord ++ tailWord_489066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489096 : List Nat := [2, 1, 3, 5, 1, 1, 1, 1, 7]
def baseStart_489096 : Nat := 118140960795 + 489096 * 2 ^ 59
def prefixEnd_489096 : Nat := 4983230072969 + 3 ^ 40 * 489096 * 2
def baseEnd_489096 : Nat := 55809185375894142966821

theorem tailTrace_489096 : CollatzResearch.WordTrace tailWord_489096 prefixEnd_489096 55809185375894142966821 := by
  unfold tailWord_489096
  simp only [CollatzResearch.WordTrace]
  refine ⟨8919398318048098895835571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11892531090730798527780761 8919398318048098895835571)
  ·
    refine ⟨13379097477072148343753357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8919398318048098895835571 13379097477072148343753357)
    ·
      refine ⟨5017161553902055628907509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13379097477072148343753357 5017161553902055628907509)
      ·
        refine ⟨470358895678317715210079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5017161553902055628907509 470358895678317715210079)
        ·
          refine ⟨705538343517476572815119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470358895678317715210079 705538343517476572815119)
          ·
            refine ⟨1058307515276214859222679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 705538343517476572815119 1058307515276214859222679)
            ·
              refine ⟨1587461272914322288834019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1058307515276214859222679 1587461272914322288834019)
              ·
                refine ⟨2381191909371483433251029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1587461272914322288834019 2381191909371483433251029)
                ·
                  refine ⟨55809185375894142966821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2381191909371483433251029 55809185375894142966821)
                  ·
                    rfl

theorem cell22_489096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 7].length) (baseStart_489096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_489096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_489096 prefixEnd_489096 := by exact prefixLift 489096
  have htrace : WordTrace (prefixWord ++ tailWord_489096) baseStart_489096 baseEnd_489096 := by
    simpa [prefixWord, tailWord_489096, baseEnd_489096] using wordTrace_append hprefix tailTrace_489096
  have hstable : (prefixWord ++ tailWord_489096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489096).length < 2 ^ (prefixWord ++ tailWord_489096).sum := by decide
  have hdescent : baseEnd_489096 < baseStart_489096 := by decide
  rcases family_descends (prefixWord ++ tailWord_489096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489124 : List Nat := [2, 3, 1, 2, 2, 2, 2, 2, 6]
def baseStart_489124 : Nat := 118140960795 + 489124 * 2 ^ 59
def prefixEnd_489124 : Nat := 4983230072969 + 3 ^ 40 * 489124 * 2
def baseEnd_489124 : Nat := 55812380366633229733459

theorem tailTrace_489124 : CollatzResearch.WordTrace tailWord_489124 prefixEnd_489124 55812380366633229733459 := by
  unfold tailWord_489124
  simp only [CollatzResearch.WordTrace]
  refine ⟨8919908939997379286845213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11893211919996505715793617 8919908939997379286845213)
  ·
    refine ⟨3344965852499017232566955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8919908939997379286845213 3344965852499017232566955)
    ·
      refine ⟨5017448778748525848850433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3344965852499017232566955 5017448778748525848850433)
      ·
        refine ⟨3763086584061394386637825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5017448778748525848850433 3763086584061394386637825)
        ·
          refine ⟨2822314938046045789978369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3763086584061394386637825 2822314938046045789978369)
          ·
            refine ⟨2116736203534534342483777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2822314938046045789978369 2116736203534534342483777)
            ·
              refine ⟨1587552152650900756862833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2116736203534534342483777 1587552152650900756862833)
              ·
                refine ⟨1190664114488175567647125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1587552152650900756862833 1190664114488175567647125)
                ·
                  refine ⟨55812380366633229733459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1190664114488175567647125 55812380366633229733459)
                  ·
                    rfl

theorem cell22_489124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 2, 6].length) (baseStart_489124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_489124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_489124 prefixEnd_489124 := by exact prefixLift 489124
  have htrace : WordTrace (prefixWord ++ tailWord_489124) baseStart_489124 baseEnd_489124 := by
    simpa [prefixWord, tailWord_489124, baseEnd_489124] using wordTrace_append hprefix tailTrace_489124
  have hstable : (prefixWord ++ tailWord_489124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489124).length < 2 ^ (prefixWord ++ tailWord_489124).sum := by decide
  have hdescent : baseEnd_489124 < baseStart_489124 := by decide
  rcases family_descends (prefixWord ++ tailWord_489124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489134 : List Nat := [4, 1, 4, 1, 3, 1, 1, 3, 1, 3]
def baseStart_489134 : Nat := 118140960795 + 489134 * 2 ^ 59
def prefixEnd_489134 : Nat := 4983230072969 + 3 ^ 40 * 489134 * 2
def baseEnd_489134 : Nat := 167440564304262996450347

theorem tailTrace_489134 : CollatzResearch.WordTrace tailWord_489134 prefixEnd_489134 167440564304262996450347 := by
  unfold tailWord_489134
  simp only [CollatzResearch.WordTrace]
  refine ⟨2230022826244816285194307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11893455073305686854369637 2230022826244816285194307)
  ·
    refine ⟨3345034239367224427791461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2230022826244816285194307 3345034239367224427791461)
    ·
      refine ⟨627193919881354580210899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3345034239367224427791461 627193919881354580210899)
      ·
        refine ⟨940790879822031870316349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 627193919881354580210899 940790879822031870316349)
        ·
          refine ⟨352796579933261951368631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 940790879822031870316349 352796579933261951368631)
          ·
            refine ⟨529194869899892927052947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352796579933261951368631 529194869899892927052947)
            ·
              refine ⟨793792304849839390579421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 529194869899892927052947 793792304849839390579421)
              ·
                refine ⟨297672114318689771467283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 793792304849839390579421 297672114318689771467283)
                ·
                  refine ⟨446508171478034657200925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 297672114318689771467283 446508171478034657200925)
                  ·
                    refine ⟨167440564304262996450347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 446508171478034657200925 167440564304262996450347)
                    ·
                      rfl

theorem cell22_489134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_489134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_489134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_489134 prefixEnd_489134 := by exact prefixLift 489134
  have htrace : WordTrace (prefixWord ++ tailWord_489134) baseStart_489134 baseEnd_489134 := by
    simpa [prefixWord, tailWord_489134, baseEnd_489134] using wordTrace_append hprefix tailTrace_489134
  have hstable : (prefixWord ++ tailWord_489134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489134).length < 2 ^ (prefixWord ++ tailWord_489134).sum := by decide
  have hdescent : baseEnd_489134 < baseStart_489134 := by decide
  rcases family_descends (prefixWord ++ tailWord_489134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489139 : List Nat := [1, 1, 1, 2, 3, 3, 1, 1, 6, 3]
def baseStart_489139 : Nat := 118140960795 + 489139 * 2 ^ 59
def prefixEnd_489139 : Nat := 4983230072969 + 3 ^ 40 * 489139 * 2
def baseEnd_489139 : Nat := 167442275906444650075331

theorem tailTrace_489139 : CollatzResearch.WordTrace tailWord_489139 prefixEnd_489139 167442275906444650075331 := by
  unfold tailWord_489139
  simp only [CollatzResearch.WordTrace]
  refine ⟨17840364974940416135486471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11893576649960277423657647 17840364974940416135486471)
  ·
    refine ⟨26760547462410624203229707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17840364974940416135486471 26760547462410624203229707)
    ·
      refine ⟨40140821193615936304844561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26760547462410624203229707 40140821193615936304844561)
      ·
        refine ⟨30105615895211952228633421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40140821193615936304844561 30105615895211952228633421)
        ·
          refine ⟨11289605960704482085737533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30105615895211952228633421 11289605960704482085737533)
          ·
            refine ⟨4233602235264180782151575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11289605960704482085737533 4233602235264180782151575)
            ·
              refine ⟨6350403352896271173227363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4233602235264180782151575 6350403352896271173227363)
              ·
                refine ⟨9525605029344406759841045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6350403352896271173227363 9525605029344406759841045)
                ·
                  refine ⟨446512735750519066867549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9525605029344406759841045 446512735750519066867549)
                  ·
                    refine ⟨167442275906444650075331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 446512735750519066867549 167442275906444650075331)
                    ·
                      rfl

theorem cell22_489139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 6, 3].length) (baseStart_489139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_489139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_489139 prefixEnd_489139 := by exact prefixLift 489139
  have htrace : WordTrace (prefixWord ++ tailWord_489139) baseStart_489139 baseEnd_489139 := by
    simpa [prefixWord, tailWord_489139, baseEnd_489139] using wordTrace_append hprefix tailTrace_489139
  have hstable : (prefixWord ++ tailWord_489139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489139).length < 2 ^ (prefixWord ++ tailWord_489139).sum := by decide
  have hdescent : baseEnd_489139 < baseStart_489139 := by decide
  rcases family_descends (prefixWord ++ tailWord_489139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489156 : List Nat := [2, 3, 3, 1, 1, 1, 1, 3, 4, 3]
def baseStart_489156 : Nat := 118140960795 + 489156 * 2 ^ 59
def prefixEnd_489156 : Nat := 4983230072969 + 3 ^ 40 * 489156 * 2
def baseEnd_489156 : Nat := 167448095353862272400279

theorem tailTrace_489156 : CollatzResearch.WordTrace tailWord_489156 prefixEnd_489156 167448095353862272400279 := by
  unfold tailWord_489156
  simp only [CollatzResearch.WordTrace]
  refine ⟨8920492507939414019427661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11893990010585885359236881 8920492507939414019427661)
  ·
    refine ⟨3345184690477280257285373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8920492507939414019427661 3345184690477280257285373)
    ·
      refine ⟨1254444258928980096482015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3345184690477280257285373 1254444258928980096482015)
      ·
        refine ⟨1881666388393470144723023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1254444258928980096482015 1881666388393470144723023)
        ·
          refine ⟨2822499582590205217084535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1881666388393470144723023 2822499582590205217084535)
          ·
            refine ⟨4233749373885307825626803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2822499582590205217084535 4233749373885307825626803)
            ·
              refine ⟨6350624060827961738440205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4233749373885307825626803 6350624060827961738440205)
              ·
                refine ⟨2381484022810485651915077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6350624060827961738440205 2381484022810485651915077)
                ·
                  refine ⟨446528254276966059734077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2381484022810485651915077 446528254276966059734077)
                  ·
                    refine ⟨167448095353862272400279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 446528254276966059734077 167448095353862272400279)
                    ·
                      rfl

theorem cell22_489156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_489156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_489156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_489156 prefixEnd_489156 := by exact prefixLift 489156
  have htrace : WordTrace (prefixWord ++ tailWord_489156) baseStart_489156 baseEnd_489156 := by
    simpa [prefixWord, tailWord_489156, baseEnd_489156] using wordTrace_append hprefix tailTrace_489156
  have hstable : (prefixWord ++ tailWord_489156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489156).length < 2 ^ (prefixWord ++ tailWord_489156).sum := by decide
  have hdescent : baseEnd_489156 < baseStart_489156 := by decide
  rcases family_descends (prefixWord ++ tailWord_489156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489169 : List Nat := [1, 2, 2, 1, 2, 5, 2, 7]
def baseStart_489169 : Nat := 118140960795 + 489169 * 2 ^ 59
def prefixEnd_489169 : Nat := 4983230072969 + 3 ^ 40 * 489169 * 2
def baseEnd_489169 : Nat := 18605838391059396869471

theorem tailTrace_489169 : CollatzResearch.WordTrace tailWord_489169 prefixEnd_489169 18605838391059396869471 := by
  unfold tailWord_489169
  simp only [CollatzResearch.WordTrace]
  refine ⟨17841459164831731259078561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11894306109887820839385707 17841459164831731259078561)
  ·
    refine ⟨13381094373623798444308921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17841459164831731259078561 13381094373623798444308921)
    ·
      refine ⟨10035820780217848833231691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13381094373623798444308921 10035820780217848833231691)
      ·
        refine ⟨15053731170326773249847537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10035820780217848833231691 15053731170326773249847537)
        ·
          refine ⟨11290298377745079937385653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15053731170326773249847537 11290298377745079937385653)
          ·
            refine ⟨1058465472913601244129905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11290298377745079937385653 1058465472913601244129905)
            ·
              refine ⟨793849104685200933097429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1058465472913601244129905 793849104685200933097429)
              ·
                refine ⟨18605838391059396869471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 793849104685200933097429 18605838391059396869471)
                ·
                  rfl

theorem cell22_489169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 7].length) (baseStart_489169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_489169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_489169 prefixEnd_489169 := by exact prefixLift 489169
  have htrace : WordTrace (prefixWord ++ tailWord_489169) baseStart_489169 baseEnd_489169 := by
    simpa [prefixWord, tailWord_489169, baseEnd_489169] using wordTrace_append hprefix tailTrace_489169
  have hstable : (prefixWord ++ tailWord_489169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489169).length < 2 ^ (prefixWord ++ tailWord_489169).sum := by decide
  have hdescent : baseEnd_489169 < baseStart_489169 := by decide
  rcases family_descends (prefixWord ++ tailWord_489169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489218 : List Nat := [3, 4, 1, 1, 1, 1, 2, 3, 3, 3]
def baseStart_489218 : Nat := 118140960795 + 489218 * 2 ^ 59
def prefixEnd_489218 : Nat := 4983230072969 + 3 ^ 40 * 489218 * 2
def baseEnd_489218 : Nat := 167469319220914777350089

theorem tailTrace_489218 : CollatzResearch.WordTrace tailWord_489218 prefixEnd_489218 167469319220914777350089 := by
  unfold tailWord_489218
  simp only [CollatzResearch.WordTrace]
  refine ⟨4460811585413553156903077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11895497561102808418408205 4460811585413553156903077)
  ·
    refine ⟨836402172265041216919327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4460811585413553156903077 836402172265041216919327)
    ·
      refine ⟨1254603258397561825378991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 836402172265041216919327 1254603258397561825378991)
      ·
        refine ⟨1881904887596342738068487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1254603258397561825378991 1881904887596342738068487)
        ·
          refine ⟨2822857331394514107102731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1881904887596342738068487 2822857331394514107102731)
          ·
            refine ⟨4234285997091771160654097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2822857331394514107102731 4234285997091771160654097)
            ·
              refine ⟨3175714497818828370490573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4234285997091771160654097 3175714497818828370490573)
              ·
                refine ⟨1190892936682060638933965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3175714497818828370490573 1190892936682060638933965)
                ·
                  refine ⟨446584851255772739600237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1190892936682060638933965 446584851255772739600237)
                  ·
                    refine ⟨167469319220914777350089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 446584851255772739600237 167469319220914777350089)
                    ·
                      rfl

theorem cell22_489218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_489218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_489218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_489218 prefixEnd_489218 := by exact prefixLift 489218
  have htrace : WordTrace (prefixWord ++ tailWord_489218) baseStart_489218 baseEnd_489218 := by
    simpa [prefixWord, tailWord_489218, baseEnd_489218] using wordTrace_append hprefix tailTrace_489218
  have hstable : (prefixWord ++ tailWord_489218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489218).length < 2 ^ (prefixWord ++ tailWord_489218).sum := by decide
  have hdescent : baseEnd_489218 < baseStart_489218 := by decide
  rcases family_descends (prefixWord ++ tailWord_489218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489289 : List Nat := [1, 2, 1, 1, 2, 4, 1, 1, 3, 6]
def baseStart_489289 : Nat := 118140960795 + 489289 * 2 ^ 59
def prefixEnd_489289 : Nat := 4983230072969 + 3 ^ 40 * 489289 * 2
def baseEnd_489289 : Nat := 167493623971894258824871

theorem tailTrace_489289 : CollatzResearch.WordTrace tailWord_489289 prefixEnd_489289 167493623971894258824871 := by
  unfold tailWord_489289
  simp only [CollatzResearch.WordTrace]
  refine ⟨17845835924396991753446921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11897223949597994502297947 17845835924396991753446921)
  ·
    refine ⟨13384376943297743815085191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17845835924396991753446921 13384376943297743815085191)
    ·
      refine ⟨20076565414946615722627787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13384376943297743815085191 20076565414946615722627787)
      ·
        refine ⟨30114848122419923583941681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20076565414946615722627787 30114848122419923583941681)
        ·
          refine ⟨22586136091814942687956261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30114848122419923583941681 22586136091814942687956261)
          ·
            refine ⟨4234900517215301753991799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22586136091814942687956261 4234900517215301753991799)
            ·
              refine ⟨6352350775822952630987699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4234900517215301753991799 6352350775822952630987699)
              ·
                refine ⟨9528526163734428946481549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6352350775822952630987699 9528526163734428946481549)
                ·
                  refine ⟨3573197311400410854930581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9528526163734428946481549 3573197311400410854930581)
                  ·
                    refine ⟨167493623971894258824871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3573197311400410854930581 167493623971894258824871)
                    ·
                      rfl

theorem cell22_489289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 6].length) (baseStart_489289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_489289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_489289 prefixEnd_489289 := by exact prefixLift 489289
  have htrace : WordTrace (prefixWord ++ tailWord_489289) baseStart_489289 baseEnd_489289 := by
    simpa [prefixWord, tailWord_489289, baseEnd_489289] using wordTrace_append hprefix tailTrace_489289
  have hstable : (prefixWord ++ tailWord_489289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489289).length < 2 ^ (prefixWord ++ tailWord_489289).sum := by decide
  have hdescent : baseEnd_489289 < baseStart_489289 := by decide
  rcases family_descends (prefixWord ++ tailWord_489289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489293 : List Nat := [1, 6, 1, 2, 1, 1, 2, 2, 6]
def baseStart_489293 : Nat := 118140960795 + 489293 * 2 ^ 59
def prefixEnd_489293 : Nat := 4983230072969 + 3 ^ 40 * 489293 * 2
def baseEnd_489293 : Nat := 55831664417879860574953

theorem tailTrace_489293 : CollatzResearch.WordTrace tailWord_489293 prefixEnd_489293 55831664417879860574953 := by
  unfold tailWord_489293
  simp only [CollatzResearch.WordTrace]
  refine ⟨17845981816382500436592533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11897321210921666957728355 17845981816382500436592533)
  ·
    refine ⟨836530397642929707965275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17845981816382500436592533 836530397642929707965275)
    ·
      refine ⟨1254795596464394561947913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 836530397642929707965275 1254795596464394561947913)
      ·
        refine ⟨941096697348295921460935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1254795596464394561947913 941096697348295921460935)
        ·
          refine ⟨1411645046022443882191403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 941096697348295921460935 1411645046022443882191403)
          ·
            refine ⟨2117467569033665823287105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1411645046022443882191403 2117467569033665823287105)
            ·
              refine ⟨1588100676775249367465329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2117467569033665823287105 1588100676775249367465329)
              ·
                refine ⟨1191075507581437025598997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1588100676775249367465329 1191075507581437025598997)
                ·
                  refine ⟨55831664417879860574953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1191075507581437025598997 55831664417879860574953)
                  ·
                    rfl

theorem cell22_489293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_489293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_489293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_489293 prefixEnd_489293 := by exact prefixLift 489293
  have htrace : WordTrace (prefixWord ++ tailWord_489293) baseStart_489293 baseEnd_489293 := by
    simpa [prefixWord, tailWord_489293, baseEnd_489293] using wordTrace_append hprefix tailTrace_489293
  have hstable : (prefixWord ++ tailWord_489293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489293).length < 2 ^ (prefixWord ++ tailWord_489293).sum := by decide
  have hdescent : baseEnd_489293 < baseStart_489293 := by decide
  rcases family_descends (prefixWord ++ tailWord_489293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489306 : List Nat := [3, 1, 1, 2, 1, 3, 2, 3, 2, 4]
def baseStart_489306 : Nat := 118140960795 + 489306 * 2 ^ 59
def prefixEnd_489306 : Nat := 4983230072969 + 3 ^ 40 * 489306 * 2
def baseEnd_489306 : Nat := 167499443419311881149819

theorem tailTrace_489306 : CollatzResearch.WordTrace tailWord_489306 prefixEnd_489306 167499443419311881149819 := by
  unfold tailWord_489306
  simp only [CollatzResearch.WordTrace]
  refine ⟨4461613991333850914203943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11897637310223602437877181 4461613991333850914203943)
  ·
    refine ⟨6692420987000776371305915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4461613991333850914203943 6692420987000776371305915)
    ·
      refine ⟨10038631480501164556958873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6692420987000776371305915 10038631480501164556958873)
      ·
        refine ⟨7528973610375873417719155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10038631480501164556958873 7528973610375873417719155)
        ·
          refine ⟨11293460415563810126578733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7528973610375873417719155 11293460415563810126578733)
          ·
            refine ⟨4235047655836428797467025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11293460415563810126578733 4235047655836428797467025)
            ·
              refine ⟨3176285741877321598100269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4235047655836428797467025 3176285741877321598100269)
              ·
                refine ⟨1191107153203995599287601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3176285741877321598100269 1191107153203995599287601)
                ·
                  refine ⟨893330364902996699465701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1191107153203995599287601 893330364902996699465701)
                  ·
                    refine ⟨167499443419311881149819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 893330364902996699465701 167499443419311881149819)
                    ·
                      rfl

theorem cell22_489306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 3, 2, 4].length) (baseStart_489306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_489306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_489306 prefixEnd_489306 := by exact prefixLift 489306
  have htrace : WordTrace (prefixWord ++ tailWord_489306) baseStart_489306 baseEnd_489306 := by
    simpa [prefixWord, tailWord_489306, baseEnd_489306] using wordTrace_append hprefix tailTrace_489306
  have hstable : (prefixWord ++ tailWord_489306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489306).length < 2 ^ (prefixWord ++ tailWord_489306).sum := by decide
  have hdescent : baseEnd_489306 < baseStart_489306 := by decide
  rcases family_descends (prefixWord ++ tailWord_489306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489342 : List Nat := [4, 2, 3, 1, 1, 2, 1, 3, 2, 3]
def baseStart_489342 : Nat := 118140960795 + 489342 * 2 ^ 59
def prefixEnd_489342 : Nat := 4983230072969 + 3 ^ 40 * 489342 * 2
def baseEnd_489342 : Nat := 167511766955019787249709

theorem tailTrace_489342 : CollatzResearch.WordTrace tailWord_489342 prefixEnd_489342 167511766955019787249709 := by
  unfold tailWord_489342
  simp only [CollatzResearch.WordTrace]
  refine ⟨2230971124150622725640785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11898512662136654536750853 2230971124150622725640785)
  ·
    refine ⟨1673228343112967044230589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2230971124150622725640785 1673228343112967044230589)
    ·
      refine ⟨627460628667362641586471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1673228343112967044230589 627460628667362641586471)
      ·
        refine ⟨941190943001043962379707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 627460628667362641586471 941190943001043962379707)
        ·
          refine ⟨1411786414501565943569561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 941190943001043962379707 1411786414501565943569561)
          ·
            refine ⟨1058839810876174457677171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1411786414501565943569561 1058839810876174457677171)
            ·
              refine ⟨1588259716314261686515757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1058839810876174457677171 1588259716314261686515757)
              ·
                refine ⟨595597393617848132443409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1588259716314261686515757 595597393617848132443409)
                ·
                  refine ⟨446698045213386099332557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 595597393617848132443409 446698045213386099332557)
                  ·
                    refine ⟨167511766955019787249709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 446698045213386099332557 167511766955019787249709)
                    ·
                      rfl

theorem cell22_489342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_489342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_489342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_489342 prefixEnd_489342 := by exact prefixLift 489342
  have htrace : WordTrace (prefixWord ++ tailWord_489342) baseStart_489342 baseEnd_489342 := by
    simpa [prefixWord, tailWord_489342, baseEnd_489342] using wordTrace_append hprefix tailTrace_489342
  have hstable : (prefixWord ++ tailWord_489342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489342).length < 2 ^ (prefixWord ++ tailWord_489342).sum := by decide
  have hdescent : baseEnd_489342 < baseStart_489342 := by decide
  rcases family_descends (prefixWord ++ tailWord_489342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489383 : List Nat := [1, 1, 6, 1, 2, 1, 1, 4, 5]
def baseStart_489383 : Nat := 118140960795 + 489383 * 2 ^ 59
def prefixEnd_489383 : Nat := 4983230072969 + 3 ^ 40 * 489383 * 2
def baseEnd_489383 : Nat := 55841934030969782324861

theorem tailTrace_489383 : CollatzResearch.WordTrace tailWord_489383 prefixEnd_489383 55841934030969782324861 := by
  unfold tailWord_489383
  simp only [CollatzResearch.WordTrace]
  refine ⟨17849264386056445807368803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11899509590704297204912535 17849264386056445807368803)
  ·
    refine ⟨26773896579084668711053205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17849264386056445807368803 26773896579084668711053205)
    ·
      refine ⟨1255026402144593845830619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 26773896579084668711053205 1255026402144593845830619)
      ·
        refine ⟨1882539603216890768745929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1255026402144593845830619 1882539603216890768745929)
        ·
          refine ⟨1411904702412668076559447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1882539603216890768745929 1411904702412668076559447)
          ·
            refine ⟨2117857053619002114839171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1411904702412668076559447 2117857053619002114839171)
            ·
              refine ⟨3176785580428503172258757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2117857053619002114839171 3176785580428503172258757)
              ·
                refine ⟨595647296330344344798517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3176785580428503172258757 595647296330344344798517)
                ·
                  refine ⟨55841934030969782324861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 595647296330344344798517 55841934030969782324861)
                  ·
                    rfl

theorem cell22_489383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 4, 5].length) (baseStart_489383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_489383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_489383 prefixEnd_489383 := by exact prefixLift 489383
  have htrace : WordTrace (prefixWord ++ tailWord_489383) baseStart_489383 baseEnd_489383 := by
    simpa [prefixWord, tailWord_489383, baseEnd_489383] using wordTrace_append hprefix tailTrace_489383
  have hstable : (prefixWord ++ tailWord_489383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489383).length < 2 ^ (prefixWord ++ tailWord_489383).sum := by decide
  have hdescent : baseEnd_489383 < baseStart_489383 := by decide
  rcases family_descends (prefixWord ++ tailWord_489383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489511 : List Nat := [1, 1, 7, 1, 2, 2, 2, 1, 2, 3]
def baseStart_489511 : Nat := 118140960795 + 489511 * 2 ^ 59
def prefixEnd_489511 : Nat := 4983230072969 + 3 ^ 40 * 489511 * 2
def baseEnd_489511 : Nat := 167569619108759679774191

theorem tailTrace_489511 : CollatzResearch.WordTrace tailWord_489511 prefixEnd_489511 167569619108759679774191 := by
  unfold tailWord_489511
  simp only [CollatzResearch.WordTrace]
  refine ⟨17853932929592723668028387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11902621953061815778685591 17853932929592723668028387)
  ·
    refine ⟨26780899394389085502042581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17853932929592723668028387 26780899394389085502042581)
    ·
      refine ⟨627677329555994191454123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 26780899394389085502042581 627677329555994191454123)
      ·
        refine ⟨941515994333991287181185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 627677329555994191454123 941515994333991287181185)
        ·
          refine ⟨706136995750493465385889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 941515994333991287181185 706136995750493465385889)
          ·
            refine ⟨529602746812870099039417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 706136995750493465385889 529602746812870099039417)
            ·
              refine ⟨397202060109652574279563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 529602746812870099039417 397202060109652574279563)
              ·
                refine ⟨595803090164478861419345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 397202060109652574279563 595803090164478861419345)
                ·
                  refine ⟨446852317623359146064509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 595803090164478861419345 446852317623359146064509)
                  ·
                    refine ⟨167569619108759679774191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 446852317623359146064509 167569619108759679774191)
                    ·
                      rfl

theorem cell22_489511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_489511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_489511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_489511 prefixEnd_489511 := by exact prefixLift 489511
  have htrace : WordTrace (prefixWord ++ tailWord_489511) baseStart_489511 baseEnd_489511 := by
    simpa [prefixWord, tailWord_489511, baseEnd_489511] using wordTrace_append hprefix tailTrace_489511
  have hstable : (prefixWord ++ tailWord_489511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489511).length < 2 ^ (prefixWord ++ tailWord_489511).sum := by decide
  have hdescent : baseEnd_489511 < baseStart_489511 := by decide
  rcases family_descends (prefixWord ++ tailWord_489511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489531 : List Nat := [1, 1, 1, 1, 1, 2, 1, 4, 2, 8]
def baseStart_489531 : Nat := 118140960795 + 489531 * 2 ^ 59
def prefixEnd_489531 : Nat := 4983230072969 + 3 ^ 40 * 489531 * 2
def baseEnd_489531 : Nat := 167576465517486294274129

theorem tailTrace_489531 : CollatzResearch.WordTrace tailWord_489531 prefixEnd_489531 167576465517486294274129 := by
  unfold tailWord_489531
  simp only [CollatzResearch.WordTrace]
  refine ⟨17854662389520267083756447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11903108259680178055837631 17854662389520267083756447)
  ·
    refine ⟨26781993584280400625634671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17854662389520267083756447 26781993584280400625634671)
    ·
      refine ⟨40172990376420600938452007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26781993584280400625634671 40172990376420600938452007)
      ·
        refine ⟨60259485564630901407678011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40172990376420600938452007 60259485564630901407678011)
        ·
          refine ⟨90389228346946352111517017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60259485564630901407678011 90389228346946352111517017)
          ·
            refine ⟨67791921260209764083637763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90389228346946352111517017 67791921260209764083637763)
            ·
              refine ⟨101687881890314646125456645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67791921260209764083637763 101687881890314646125456645)
              ·
                refine ⟨19066477854433996148523121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101687881890314646125456645 19066477854433996148523121)
                ·
                  refine ⟨14299858390825497111392341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19066477854433996148523121 14299858390825497111392341)
                  ·
                    refine ⟨167576465517486294274129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 14299858390825497111392341 167576465517486294274129)
                    ·
                      rfl

theorem cell22_489531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 8].length) (baseStart_489531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_489531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_489531 prefixEnd_489531 := by exact prefixLift 489531
  have htrace : WordTrace (prefixWord ++ tailWord_489531) baseStart_489531 baseEnd_489531 := by
    simpa [prefixWord, tailWord_489531, baseEnd_489531] using wordTrace_append hprefix tailTrace_489531
  have hstable : (prefixWord ++ tailWord_489531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489531).length < 2 ^ (prefixWord ++ tailWord_489531).sum := by decide
  have hdescent : baseEnd_489531 < baseStart_489531 := by decide
  rcases family_descends (prefixWord ++ tailWord_489531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489597 : List Nat := [1, 4, 1, 1, 3, 3, 2, 3, 4]
def baseStart_489597 : Nat := 118140960795 + 489597 * 2 ^ 59
def prefixEnd_489597 : Nat := 4983230072969 + 3 ^ 40 * 489597 * 2
def baseEnd_489597 : Nat := 55866352888761374041309

theorem tailTrace_489597 : CollatzResearch.WordTrace tailWord_489597 prefixEnd_489597 55866352888761374041309 := by
  unfold tailWord_489597
  simp only [CollatzResearch.WordTrace]
  refine ⟨17857069607281160355659045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11904713071520773570439363 17857069607281160355659045)
  ·
    refine ⟨3348200551365217566686071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17857069607281160355659045 3348200551365217566686071)
    ·
      refine ⟨5022300827047826350029107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3348200551365217566686071 5022300827047826350029107)
      ·
        refine ⟨7533451240571739525043661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5022300827047826350029107 7533451240571739525043661)
        ·
          refine ⟨2825044215214402321891373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7533451240571739525043661 2825044215214402321891373)
          ·
            refine ⟨1059391580705400870709265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2825044215214402321891373 1059391580705400870709265)
            ·
              refine ⟨794543685529050653031949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1059391580705400870709265 794543685529050653031949)
              ·
                refine ⟨297953882073393994886981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 794543685529050653031949 297953882073393994886981)
                ·
                  refine ⟨55866352888761374041309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 297953882073393994886981 55866352888761374041309)
                  ·
                    rfl

theorem cell22_489597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 3, 4].length) (baseStart_489597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_489597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_489597 prefixEnd_489597 := by exact prefixLift 489597
  have htrace : WordTrace (prefixWord ++ tailWord_489597) baseStart_489597 baseEnd_489597 := by
    simpa [prefixWord, tailWord_489597, baseEnd_489597] using wordTrace_append hprefix tailTrace_489597
  have hstable : (prefixWord ++ tailWord_489597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489597).length < 2 ^ (prefixWord ++ tailWord_489597).sum := by decide
  have hdescent : baseEnd_489597 < baseStart_489597 := by decide
  rcases family_descends (prefixWord ++ tailWord_489597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489629 : List Nat := [1, 4, 2, 1, 1, 4, 3, 1, 2, 3]
def baseStart_489629 : Nat := 118140960795 + 489629 * 2 ^ 59
def prefixEnd_489629 : Nat := 4983230072969 + 3 ^ 40 * 489629 * 2
def baseEnd_489629 : Nat := 167610012920246705323829

theorem tailTrace_489629 : CollatzResearch.WordTrace tailWord_489629 prefixEnd_489629 167610012920246705323829 := by
  unfold tailWord_489629
  simp only [CollatzResearch.WordTrace]
  refine ⟨17858236743165229820823941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11905491162110153213882627 17858236743165229820823941)
  ·
    refine ⟨3348419389343480591404489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17858236743165229820823941 3348419389343480591404489)
    ·
      refine ⟨2511314542007610443553367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3348419389343480591404489 2511314542007610443553367)
      ·
        refine ⟨3766971813011415665330051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2511314542007610443553367 3766971813011415665330051)
        ·
          refine ⟨5650457719517123497995077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3766971813011415665330051 5650457719517123497995077)
          ·
            refine ⟨1059460822409460655874077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5650457719517123497995077 1059460822409460655874077)
            ·
              refine ⟨397297808403547745952779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1059460822409460655874077 397297808403547745952779)
              ·
                refine ⟨595946712605321618929169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 397297808403547745952779 595946712605321618929169)
                ·
                  refine ⟨446960034453991214196877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 595946712605321618929169 446960034453991214196877)
                  ·
                    refine ⟨167610012920246705323829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 446960034453991214196877 167610012920246705323829)
                    ·
                      rfl

theorem cell22_489629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 3, 1, 2, 3].length) (baseStart_489629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_489629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_489629 prefixEnd_489629 := by exact prefixLift 489629
  have htrace : WordTrace (prefixWord ++ tailWord_489629) baseStart_489629 baseEnd_489629 := by
    simpa [prefixWord, tailWord_489629, baseEnd_489629] using wordTrace_append hprefix tailTrace_489629
  have hstable : (prefixWord ++ tailWord_489629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489629).length < 2 ^ (prefixWord ++ tailWord_489629).sum := by decide
  have hdescent : baseEnd_489629 < baseStart_489629 := by decide
  rcases family_descends (prefixWord ++ tailWord_489629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489642 : List Nat := [3, 1, 5, 1, 2, 1, 1, 8]
def baseStart_489642 : Nat := 118140960795 + 489642 * 2 ^ 59
def prefixEnd_489642 : Nat := 4983230072969 + 3 ^ 40 * 489642 * 2
def baseEnd_489642 : Nat := 18623829231768778305421

theorem tailTrace_489642 : CollatzResearch.WordTrace tailWord_489642 prefixEnd_489642 18623829231768778305421 := by
  unfold tailWord_489642
  simp only [CollatzResearch.WordTrace]
  refine ⟨4464677723029533260261795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11905807261412088694031453 4464677723029533260261795)
  ·
    refine ⟨6697016584544299890392693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4464677723029533260261795 6697016584544299890392693)
    ·
      refine ⟨627845304801028114724315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6697016584544299890392693 627845304801028114724315)
      ·
        refine ⟨941767957201542172086473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 627845304801028114724315 941767957201542172086473)
        ·
          refine ⟨706325967901156629064855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 941767957201542172086473 706325967901156629064855)
          ·
            refine ⟨1059488951851734943597283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 706325967901156629064855 1059488951851734943597283)
            ·
              refine ⟨1589233427777602415395925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1059488951851734943597283 1589233427777602415395925)
              ·
                refine ⟨18623829231768778305421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1589233427777602415395925 18623829231768778305421)
                ·
                  rfl

theorem cell22_489642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 8].length) (baseStart_489642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_489642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_489642 prefixEnd_489642 := by exact prefixLift 489642
  have htrace : WordTrace (prefixWord ++ tailWord_489642) baseStart_489642 baseEnd_489642 := by
    simpa [prefixWord, tailWord_489642, baseEnd_489642] using wordTrace_append hprefix tailTrace_489642
  have hstable : (prefixWord ++ tailWord_489642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489642).length < 2 ^ (prefixWord ++ tailWord_489642).sum := by decide
  have hdescent : baseEnd_489642 < baseStart_489642 := by decide
  rcases family_descends (prefixWord ++ tailWord_489642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489762 : List Nat := [3, 3, 1, 1, 3, 2, 1, 1, 1, 6]
def baseStart_489762 : Nat := 118140960795 + 489762 * 2 ^ 59
def prefixEnd_489762 : Nat := 4983230072969 + 3 ^ 40 * 489762 * 2
def baseEnd_489762 : Nat := 167655541538278691748421

theorem tailTrace_489762 : CollatzResearch.WordTrace tailWord_489762 prefixEnd_489762 167655541538278691748421 := by
  unfold tailWord_489762
  simp only [CollatzResearch.WordTrace]
  refine ⟨4465771912920848383853885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11908725101122262356943693 4465771912920848383853885)
  ·
    refine ⟨1674664467345318143945207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4465771912920848383853885 1674664467345318143945207)
    ·
      refine ⟨2511996701017977215917811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1674664467345318143945207 2511996701017977215917811)
      ·
        refine ⟨3767995051526965823876717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2511996701017977215917811 3767995051526965823876717)
        ·
          refine ⟨1412998144322612183953769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3767995051526965823876717 1412998144322612183953769)
          ·
            refine ⟨1059748608241959137965327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1412998144322612183953769 1059748608241959137965327)
            ·
              refine ⟨1589622912362938706947991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1059748608241959137965327 1589622912362938706947991)
              ·
                refine ⟨2384434368544408060421987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1589622912362938706947991 2384434368544408060421987)
                ·
                  refine ⟨3576651552816612090632981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2384434368544408060421987 3576651552816612090632981)
                  ·
                    refine ⟨167655541538278691748421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3576651552816612090632981 167655541538278691748421)
                    ·
                      rfl

theorem cell22_489762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_489762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_489762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_489762 prefixEnd_489762 := by exact prefixLift 489762
  have htrace : WordTrace (prefixWord ++ tailWord_489762) baseStart_489762 baseEnd_489762 := by
    simpa [prefixWord, tailWord_489762, baseEnd_489762] using wordTrace_append hprefix tailTrace_489762
  have hstable : (prefixWord ++ tailWord_489762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489762).length < 2 ^ (prefixWord ++ tailWord_489762).sum := by decide
  have hdescent : baseEnd_489762 < baseStart_489762 := by decide
  rcases family_descends (prefixWord ++ tailWord_489762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489768 : List Nat := [2, 1, 5, 1, 4, 1, 2, 1, 1, 4]
def baseStart_489768 : Nat := 118140960795 + 489768 * 2 ^ 59
def prefixEnd_489768 : Nat := 4983230072969 + 3 ^ 40 * 489768 * 2
def baseEnd_489768 : Nat := 167657595460896676098403

theorem tailTrace_489768 : CollatzResearch.WordTrace tailWord_489768 prefixEnd_489768 167657595460896676098403 := by
  unfold tailWord_489768
  simp only [CollatzResearch.WordTrace]
  refine ⟨8931653244830828280066979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11908870993107771040089305 8931653244830828280066979)
  ·
    refine ⟨13397479867246242420100469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8931653244830828280066979 13397479867246242420100469)
    ·
      refine ⟨1256013737554335226884419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13397479867246242420100469 1256013737554335226884419)
      ·
        refine ⟨1884020606331502840326629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1256013737554335226884419 1884020606331502840326629)
        ·
          refine ⟨353253863687156782561243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1884020606331502840326629 353253863687156782561243)
          ·
            refine ⟨529880795530735173841865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353253863687156782561243 529880795530735173841865)
            ·
              refine ⟨397410596648051380381399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 529880795530735173841865 397410596648051380381399)
              ·
                refine ⟨596115894972077070572099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 397410596648051380381399 596115894972077070572099)
                ·
                  refine ⟨894173842458115605858149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 596115894972077070572099 894173842458115605858149)
                  ·
                    refine ⟨167657595460896676098403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 894173842458115605858149 167657595460896676098403)
                    ·
                      rfl

theorem cell22_489768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_489768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_489768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_489768 prefixEnd_489768 := by exact prefixLift 489768
  have htrace : WordTrace (prefixWord ++ tailWord_489768) baseStart_489768 baseEnd_489768 := by
    simpa [prefixWord, tailWord_489768, baseEnd_489768] using wordTrace_append hprefix tailTrace_489768
  have hstable : (prefixWord ++ tailWord_489768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489768).length < 2 ^ (prefixWord ++ tailWord_489768).sum := by decide
  have hdescent : baseEnd_489768 < baseStart_489768 := by decide
  rcases family_descends (prefixWord ++ tailWord_489768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489882 : List Nat := [3, 1, 1, 4, 1, 2, 1, 1, 3, 5]
def baseStart_489882 : Nat := 118140960795 + 489882 * 2 ^ 59
def prefixEnd_489882 : Nat := 4983230072969 + 3 ^ 40 * 489882 * 2
def baseEnd_489882 : Nat := 167696619990638378748053

theorem tailTrace_489882 : CollatzResearch.WordTrace tailWord_489882 prefixEnd_489882 167696619990638378748053 := by
  unfold tailWord_489882
  simp only [CollatzResearch.WordTrace]
  refine ⟨4466866102812163507445975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11911642940832436019855933 4466866102812163507445975)
  ·
    refine ⟨6700299154218245261168963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4466866102812163507445975 6700299154218245261168963)
    ·
      refine ⟨10050448731327367891753445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6700299154218245261168963 10050448731327367891753445)
      ·
        refine ⟨1884459137123881479703771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10050448731327367891753445 1884459137123881479703771)
        ·
          refine ⟨2826688705685822219555657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1884459137123881479703771 2826688705685822219555657)
          ·
            refine ⟨2120016529264366664666743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2826688705685822219555657 2120016529264366664666743)
            ·
              refine ⟨3180024793896549997000115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2120016529264366664666743 3180024793896549997000115)
              ·
                refine ⟨4770037190844824995500173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3180024793896549997000115 4770037190844824995500173)
                ·
                  refine ⟨1788763946566809373312565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4770037190844824995500173 1788763946566809373312565)
                  ·
                    refine ⟨167696619990638378748053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1788763946566809373312565 167696619990638378748053)
                    ·
                      rfl

theorem cell22_489882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 3, 5].length) (baseStart_489882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_489882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_489882 prefixEnd_489882 := by exact prefixLift 489882
  have htrace : WordTrace (prefixWord ++ tailWord_489882) baseStart_489882 baseEnd_489882 := by
    simpa [prefixWord, tailWord_489882, baseEnd_489882] using wordTrace_append hprefix tailTrace_489882
  have hstable : (prefixWord ++ tailWord_489882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489882).length < 2 ^ (prefixWord ++ tailWord_489882).sum := by decide
  have hdescent : baseEnd_489882 < baseStart_489882 := by decide
  rcases family_descends (prefixWord ++ tailWord_489882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489916 : List Nat := [2, 2, 2, 4, 1, 1, 2, 3, 2, 3]
def baseStart_489916 : Nat := 118140960795 + 489916 * 2 ^ 59
def prefixEnd_489916 : Nat := 4983230072969 + 3 ^ 40 * 489916 * 2
def baseEnd_489916 : Nat := 167708258885473623397949

theorem tailTrace_489916 : CollatzResearch.WordTrace tailWord_489916 prefixEnd_489916 167708258885473623397949 := by
  unfold tailWord_489916
  simp only [CollatzResearch.WordTrace]
  refine ⟨8934352246562738918260801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11912469662083651891014401 8934352246562738918260801)
  ·
    refine ⟨6700764184922054188695601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8934352246562738918260801 6700764184922054188695601)
    ·
      refine ⟨5025573138691540641521701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6700764184922054188695601 5025573138691540641521701)
      ·
        refine ⟨942294963504663870285319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5025573138691540641521701 942294963504663870285319)
        ·
          refine ⟨1413442445256995805427979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 942294963504663870285319 1413442445256995805427979)
          ·
            refine ⟨2120163667885493708141969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1413442445256995805427979 2120163667885493708141969)
            ·
              refine ⟨1590122750914120281106477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2120163667885493708141969 1590122750914120281106477)
              ·
                refine ⟨596296031592795105414929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1590122750914120281106477 596296031592795105414929)
                ·
                  refine ⟨447222023694596329061197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 596296031592795105414929 447222023694596329061197)
                  ·
                    refine ⟨167708258885473623397949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 447222023694596329061197 167708258885473623397949)
                    ·
                      rfl

theorem cell22_489916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 3, 2, 3].length) (baseStart_489916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_489916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_489916 prefixEnd_489916 := by exact prefixLift 489916
  have htrace : WordTrace (prefixWord ++ tailWord_489916) baseStart_489916 baseEnd_489916 := by
    simpa [prefixWord, tailWord_489916, baseEnd_489916] using wordTrace_append hprefix tailTrace_489916
  have hstable : (prefixWord ++ tailWord_489916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489916).length < 2 ^ (prefixWord ++ tailWord_489916).sum := by decide
  have hdescent : baseEnd_489916 < baseStart_489916 := by decide
  rcases family_descends (prefixWord ++ tailWord_489916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490019 : List Nat := [1, 1, 1, 4, 4, 1, 3, 1, 6]
def baseStart_490019 : Nat := 118140960795 + 490019 * 2 ^ 59
def prefixEnd_490019 : Nat := 4983230072969 + 3 ^ 40 * 490019 * 2
def baseEnd_490019 : Nat := 55914505963471896024211

theorem tailTrace_490019 : CollatzResearch.WordTrace tailWord_490019 prefixEnd_490019 55914505963471896024211 := by
  unfold tailWord_490019
  simp only [CollatzResearch.WordTrace]
  refine ⟨17872461211752326427521111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11914974141168217618347407 17872461211752326427521111)
  ·
    refine ⟨26808691817628489641281667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17872461211752326427521111 26808691817628489641281667)
    ·
      refine ⟨40213037726442734461922501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26808691817628489641281667 40213037726442734461922501)
      ·
        refine ⟨7539944573708012711610469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40213037726442734461922501 7539944573708012711610469)
        ·
          refine ⟨1413739607570252383426963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7539944573708012711610469 1413739607570252383426963)
          ·
            refine ⟨2120609411355378575140445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1413739607570252383426963 2120609411355378575140445)
            ·
              refine ⟨795228529258266965677667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2120609411355378575140445 795228529258266965677667)
              ·
                refine ⟨1192842793887400448516501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 795228529258266965677667 1192842793887400448516501)
                ·
                  refine ⟨55914505963471896024211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1192842793887400448516501 55914505963471896024211)
                  ·
                    rfl

theorem cell22_490019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 1, 6].length) (baseStart_490019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_490019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_490019 prefixEnd_490019 := by exact prefixLift 490019
  have htrace : WordTrace (prefixWord ++ tailWord_490019) baseStart_490019 baseEnd_490019 := by
    simpa [prefixWord, tailWord_490019, baseEnd_490019] using wordTrace_append hprefix tailTrace_490019
  have hstable : (prefixWord ++ tailWord_490019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490019).length < 2 ^ (prefixWord ++ tailWord_490019).sum := by decide
  have hdescent : baseEnd_490019 < baseStart_490019 := by decide
  rcases family_descends (prefixWord ++ tailWord_490019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490032 : List Nat := [2, 1, 1, 1, 2, 3, 2, 1, 3, 6]
def baseStart_490032 : Nat := 118140960795 + 490032 * 2 ^ 59
def prefixEnd_490032 : Nat := 4983230072969 + 3 ^ 40 * 490032 * 2
def baseEnd_490032 : Nat := 167747968056087987497593

theorem tailTrace_490032 : CollatzResearch.WordTrace tailWord_490032 prefixEnd_490032 167747968056087987497593 := by
  unfold tailWord_490032
  simp only [CollatzResearch.WordTrace]
  refine ⟨8936467680352614823872175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11915290240470153098496233 8936467680352614823872175)
  ·
    refine ⟨13404701520528922235808263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8936467680352614823872175 13404701520528922235808263)
    ·
      refine ⟨20107052280793383353712395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13404701520528922235808263 20107052280793383353712395)
      ·
        refine ⟨30160578421190075030568593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20107052280793383353712395 30160578421190075030568593)
        ·
          refine ⟨22620433815892556272926445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30160578421190075030568593 22620433815892556272926445)
          ·
            refine ⟨8482662680959708602347417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22620433815892556272926445 8482662680959708602347417)
            ·
              refine ⟨6361997010719781451760563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8482662680959708602347417 6361997010719781451760563)
              ·
                refine ⟨9542995516079672177640845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6361997010719781451760563 9542995516079672177640845)
                ·
                  refine ⟨3578623318529877066615317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9542995516079672177640845 3578623318529877066615317)
                  ·
                    refine ⟨167747968056087987497593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3578623318529877066615317 167747968056087987497593)
                    ·
                      rfl

theorem cell22_490032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 3, 6].length) (baseStart_490032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_490032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_490032 prefixEnd_490032 := by exact prefixLift 490032
  have htrace : WordTrace (prefixWord ++ tailWord_490032) baseStart_490032 baseEnd_490032 := by
    simpa [prefixWord, tailWord_490032, baseEnd_490032] using wordTrace_append hprefix tailTrace_490032
  have hstable : (prefixWord ++ tailWord_490032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490032).length < 2 ^ (prefixWord ++ tailWord_490032).sum := by decide
  have hdescent : baseEnd_490032 < baseStart_490032 := by decide
  rcases family_descends (prefixWord ++ tailWord_490032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490038 : List Nat := [5, 1, 2, 1, 2, 1, 3, 2, 1, 4]
def baseStart_490038 : Nat := 118140960795 + 490038 * 2 ^ 59
def prefixEnd_490038 : Nat := 4983230072969 + 3 ^ 40 * 490038 * 2
def baseEnd_490038 : Nat := 167750021978705971847575

theorem tailTrace_490038 : CollatzResearch.WordTrace tailWord_490038 prefixEnd_490038 167750021978705971847575 := by
  unfold tailWord_490038
  simp only [CollatzResearch.WordTrace]
  refine ⟨1117072137417718292028923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11915436132455661781641845 1117072137417718292028923)
  ·
    refine ⟨1675608206126577438043385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1117072137417718292028923 1675608206126577438043385)
    ·
      refine ⟨1256706154594933078532539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1675608206126577438043385 1256706154594933078532539)
      ·
        refine ⟨1885059231892399617798809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1256706154594933078532539 1885059231892399617798809)
        ·
          refine ⟨1413794423919299713349107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1885059231892399617798809 1413794423919299713349107)
          ·
            refine ⟨2120691635878949570023661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1413794423919299713349107 2120691635878949570023661)
            ·
              refine ⟨795259363454606088758873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2120691635878949570023661 795259363454606088758873)
              ·
                refine ⟨596444522590954566569155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 795259363454606088758873 596444522590954566569155)
                ·
                  refine ⟨894666783886431849853733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 596444522590954566569155 894666783886431849853733)
                  ·
                    refine ⟨167750021978705971847575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 894666783886431849853733 167750021978705971847575)
                    ·
                      rfl

theorem cell22_490038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_490038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_490038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_490038 prefixEnd_490038 := by exact prefixLift 490038
  have htrace : WordTrace (prefixWord ++ tailWord_490038) baseStart_490038 baseEnd_490038 := by
    simpa [prefixWord, tailWord_490038, baseEnd_490038] using wordTrace_append hprefix tailTrace_490038
  have hstable : (prefixWord ++ tailWord_490038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490038).length < 2 ^ (prefixWord ++ tailWord_490038).sum := by decide
  have hdescent : baseEnd_490038 < baseStart_490038 := by decide
  rcases family_descends (prefixWord ++ tailWord_490038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490047 : List Nat := [1, 1, 2, 2, 3, 2, 1, 10]
def baseStart_490047 : Nat := 118140960795 + 490047 * 2 ^ 59
def prefixEnd_490047 : Nat := 4983230072969 + 3 ^ 40 * 490047 * 2
def baseEnd_490047 : Nat := 18639233651403660930283

theorem tailTrace_490047 : CollatzResearch.WordTrace tailWord_490047 prefixEnd_490047 18639233651403660930283 := by
  unfold tailWord_490047
  simp only [CollatzResearch.WordTrace]
  refine ⟨17873482455650887209540395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11915654970433924806360263 17873482455650887209540395)
  ·
    refine ⟨26810223683476330814310593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17873482455650887209540395 26810223683476330814310593)
    ·
      refine ⟨20107667762607248110732945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26810223683476330814310593 20107667762607248110732945)
      ·
        refine ⟨15080750821955436083049709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20107667762607248110732945 15080750821955436083049709)
        ·
          refine ⟨5655281558233288531143641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15080750821955436083049709 5655281558233288531143641)
          ·
            refine ⟨4241461168674966398357731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5655281558233288531143641 4241461168674966398357731)
            ·
              refine ⟨6362191753012449597536597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4241461168674966398357731 6362191753012449597536597)
              ·
                refine ⟨18639233651403660930283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 6362191753012449597536597 18639233651403660930283)
                ·
                  rfl

theorem cell22_490047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 10].length) (baseStart_490047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_490047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_490047 prefixEnd_490047 := by exact prefixLift 490047
  have htrace : WordTrace (prefixWord ++ tailWord_490047) baseStart_490047 baseEnd_490047 := by
    simpa [prefixWord, tailWord_490047, baseEnd_490047] using wordTrace_append hprefix tailTrace_490047
  have hstable : (prefixWord ++ tailWord_490047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490047).length < 2 ^ (prefixWord ++ tailWord_490047).sum := by decide
  have hdescent : baseEnd_490047 < baseStart_490047 := by decide
  rcases family_descends (prefixWord ++ tailWord_490047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490068 : List Nat := [2, 4, 1, 1, 1, 4, 2, 2, 2, 3]
def baseStart_490068 : Nat := 118140960795 + 490068 * 2 ^ 59
def prefixEnd_490068 : Nat := 4983230072969 + 3 ^ 40 * 490068 * 2
def baseEnd_490068 : Nat := 167760291591795893597483

theorem tailTrace_490068 : CollatzResearch.WordTrace tailWord_490068 prefixEnd_490068 167760291591795893597483 := by
  unfold tailWord_490068
  simp only [CollatzResearch.WordTrace]
  refine ⟨8937124194287403898027429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11916165592383205197369905 8937124194287403898027429)
  ·
    refine ⟨1675710786428888230880143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8937124194287403898027429 1675710786428888230880143)
    ·
      refine ⟨2513566179643332346320215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1675710786428888230880143 2513566179643332346320215)
      ·
        refine ⟨3770349269464998519480323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2513566179643332346320215 3770349269464998519480323)
        ·
          refine ⟨5655523904197497779220485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3770349269464998519480323 5655523904197497779220485)
          ·
            refine ⟨1060410732037030833603841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5655523904197497779220485 1060410732037030833603841)
            ·
              refine ⟨795308049027773125202881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1060410732037030833603841 795308049027773125202881)
              ·
                refine ⟨596481036770829843902161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 795308049027773125202881 596481036770829843902161)
                ·
                  refine ⟨447360777578122382926621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 596481036770829843902161 447360777578122382926621)
                  ·
                    refine ⟨167760291591795893597483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 447360777578122382926621 167760291591795893597483)
                    ·
                      rfl

theorem cell22_490068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_490068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_490068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_490068 prefixEnd_490068 := by exact prefixLift 490068
  have htrace : WordTrace (prefixWord ++ tailWord_490068) baseStart_490068 baseEnd_490068 := by
    simpa [prefixWord, tailWord_490068, baseEnd_490068] using wordTrace_append hprefix tailTrace_490068
  have hstable : (prefixWord ++ tailWord_490068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490068).length < 2 ^ (prefixWord ++ tailWord_490068).sum := by decide
  have hdescent : baseEnd_490068 < baseStart_490068 := by decide
  rcases family_descends (prefixWord ++ tailWord_490068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490079 : List Nat := [1, 1, 2, 3, 1, 1, 1, 2, 7, 3]
def baseStart_490079 : Nat := 118140960795 + 490079 * 2 ^ 59
def prefixEnd_490079 : Nat := 4983230072969 + 3 ^ 40 * 490079 * 2
def baseEnd_490079 : Nat := 167764057116595531572449

theorem tailTrace_490079 : CollatzResearch.WordTrace tailWord_490079 prefixEnd_490079 167764057116595531572449 := by
  unfold tailWord_490079
  simp only [CollatzResearch.WordTrace]
  refine ⟨17874649591534956674705291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11916433061023304449803527 17874649591534956674705291)
  ·
    refine ⟨26811974387302435012057937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17874649591534956674705291 26811974387302435012057937)
    ·
      refine ⟨20108980790476826259043453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26811974387302435012057937 20108980790476826259043453)
      ·
        refine ⟨7540867796428809847141295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20108980790476826259043453 7540867796428809847141295)
        ·
          refine ⟨11311301694643214770711943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7540867796428809847141295 11311301694643214770711943)
          ·
            refine ⟨16966952541964822156067915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11311301694643214770711943 16966952541964822156067915)
            ·
              refine ⟨25450428812947233234101873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16966952541964822156067915 25450428812947233234101873)
              ·
                refine ⟨19087821609710424925576405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25450428812947233234101873 19087821609710424925576405)
                ·
                  refine ⟨447370818977588084193197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19087821609710424925576405 447370818977588084193197)
                  ·
                    refine ⟨167764057116595531572449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 447370818977588084193197 167764057116595531572449)
                    ·
                      rfl

theorem cell22_490079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 7, 3].length) (baseStart_490079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_490079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_490079 prefixEnd_490079 := by exact prefixLift 490079
  have htrace : WordTrace (prefixWord ++ tailWord_490079) baseStart_490079 baseEnd_490079 := by
    simpa [prefixWord, tailWord_490079, baseEnd_490079] using wordTrace_append hprefix tailTrace_490079
  have hstable : (prefixWord ++ tailWord_490079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490079).length < 2 ^ (prefixWord ++ tailWord_490079).sum := by decide
  have hdescent : baseEnd_490079 < baseStart_490079 := by decide
  rcases family_descends (prefixWord ++ tailWord_490079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490130 : List Nat := [3, 2, 3, 1, 2, 1, 2, 4, 1, 3]
def baseStart_490130 : Nat := 118140960795 + 490130 * 2 ^ 59
def prefixEnd_490130 : Nat := 4983230072969 + 3 ^ 40 * 490130 * 2
def baseEnd_490130 : Nat := 167781515458848398547293

theorem tailTrace_490130 : CollatzResearch.WordTrace tailWord_490130 prefixEnd_490130 167781515458848398547293 := by
  unfold tailWord_490130
  simp only [CollatzResearch.WordTrace]
  refine ⟨4469127428587548096202961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11917673142900128256541229 4469127428587548096202961)
  ·
    refine ⟨3351845571440661072152221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4469127428587548096202961 3351845571440661072152221)
    ·
      refine ⟨1256942089290247902057083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3351845571440661072152221 1256942089290247902057083)
      ·
        refine ⟨1885413133935371853085625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1256942089290247902057083 1885413133935371853085625)
        ·
          refine ⟨1414059850451528889814219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1885413133935371853085625 1414059850451528889814219)
          ·
            refine ⟨2121089775677293334721329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1414059850451528889814219 2121089775677293334721329)
            ·
              refine ⟨1590817331757970001040997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2121089775677293334721329 1590817331757970001040997)
              ·
                refine ⟨298278249704619375195187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1590817331757970001040997 298278249704619375195187)
                ·
                  refine ⟨447417374556929062792781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 298278249704619375195187 447417374556929062792781)
                  ·
                    refine ⟨167781515458848398547293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 447417374556929062792781 167781515458848398547293)
                    ·
                      rfl

theorem cell22_490130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_490130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_490130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_490130 prefixEnd_490130 := by exact prefixLift 490130
  have htrace : WordTrace (prefixWord ++ tailWord_490130) baseStart_490130 baseEnd_490130 := by
    simpa [prefixWord, tailWord_490130, baseEnd_490130] using wordTrace_append hprefix tailTrace_490130
  have hstable : (prefixWord ++ tailWord_490130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490130).length < 2 ^ (prefixWord ++ tailWord_490130).sum := by decide
  have hdescent : baseEnd_490130 < baseStart_490130 := by decide
  rcases family_descends (prefixWord ++ tailWord_490130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490169 : List Nat := [1, 2, 1, 4, 1, 1, 1, 3, 3, 5]
def baseStart_490169 : Nat := 118140960795 + 490169 * 2 ^ 59
def prefixEnd_490169 : Nat := 4983230072969 + 3 ^ 40 * 490169 * 2
def baseEnd_490169 : Nat := 167794865955865296822173

theorem tailTrace_490169 : CollatzResearch.WordTrace tailWord_490169 prefixEnd_490169 167794865955865296822173 := by
  unfold tailWord_490169
  simp only [CollatzResearch.WordTrace]
  refine ⟨17877932161208902045481561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11918621440805934696987707 17877932161208902045481561)
  ·
    refine ⟨13408449120906676534111171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17877932161208902045481561 13408449120906676534111171)
    ·
      refine ⟨20112673681360014801166757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13408449120906676534111171 20112673681360014801166757)
      ·
        refine ⟨3771126315255002775218767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20112673681360014801166757 3771126315255002775218767)
        ·
          refine ⟨5656689472882504162828151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3771126315255002775218767 5656689472882504162828151)
          ·
            refine ⟨8485034209323756244242227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5656689472882504162828151 8485034209323756244242227)
            ·
              refine ⟨12727551313985634366363341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8485034209323756244242227 12727551313985634366363341)
              ·
                refine ⟨4772831742744612887386253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12727551313985634366363341 4772831742744612887386253)
                ·
                  refine ⟨1789811903529229832769845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4772831742744612887386253 1789811903529229832769845)
                  ·
                    refine ⟨167794865955865296822173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1789811903529229832769845 167794865955865296822173)
                    ·
                      rfl

theorem cell22_490169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 3, 5].length) (baseStart_490169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_490169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_490169 prefixEnd_490169 := by exact prefixLift 490169
  have htrace : WordTrace (prefixWord ++ tailWord_490169) baseStart_490169 baseEnd_490169 := by
    simpa [prefixWord, tailWord_490169, baseEnd_490169] using wordTrace_append hprefix tailTrace_490169
  have hstable : (prefixWord ++ tailWord_490169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490169).length < 2 ^ (prefixWord ++ tailWord_490169).sum := by decide
  have hdescent : baseEnd_490169 < baseStart_490169 := by decide
  rcases family_descends (prefixWord ++ tailWord_490169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490188 : List Nat := [2, 2, 1, 5, 1, 3, 1, 1, 6]
def baseStart_490188 : Nat := 118140960795 + 490188 * 2 ^ 59
def prefixEnd_490188 : Nat := 4983230072969 + 3 ^ 40 * 490188 * 2
def baseEnd_490188 : Nat := 55933790014718526865705

theorem tailTrace_490188 : CollatzResearch.WordTrace tailWord_490188 prefixEnd_490188 55933790014718526865705 := by
  unfold tailWord_490188
  simp only [CollatzResearch.WordTrace]
  refine ⟨8939312574070034145211609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11919083432093378860282145 8939312574070034145211609)
  ·
    refine ⟨6704484430552525608908707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8939312574070034145211609 6704484430552525608908707)
    ·
      refine ⟨10056726645828788413363061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6704484430552525608908707 10056726645828788413363061)
      ·
        refine ⟨942818123046448913752787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10056726645828788413363061 942818123046448913752787)
        ·
          refine ⟨1414227184569673370629181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 942818123046448913752787 1414227184569673370629181)
          ·
            refine ⟨530335194213627513985943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1414227184569673370629181 530335194213627513985943)
            ·
              refine ⟨795502791320441270978915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 530335194213627513985943 795502791320441270978915)
              ·
                refine ⟨1193254186980661906468373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 795502791320441270978915 1193254186980661906468373)
                ·
                  refine ⟨55933790014718526865705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1193254186980661906468373 55933790014718526865705)
                  ·
                    rfl

theorem cell22_490188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 1, 6].length) (baseStart_490188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_490188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_490188 prefixEnd_490188 := by exact prefixLift 490188
  have htrace : WordTrace (prefixWord ++ tailWord_490188) baseStart_490188 baseEnd_490188 := by
    simpa [prefixWord, tailWord_490188, baseEnd_490188] using wordTrace_append hprefix tailTrace_490188
  have hstable : (prefixWord ++ tailWord_490188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490188).length < 2 ^ (prefixWord ++ tailWord_490188).sum := by decide
  have hdescent : baseEnd_490188 < baseStart_490188 := by decide
  rcases family_descends (prefixWord ++ tailWord_490188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490199 : List Nat := [1, 1, 3, 2, 1, 4, 1, 9]
def baseStart_490199 : Nat := 118140960795 + 490199 * 2 ^ 59
def prefixEnd_490199 : Nat := 4983230072969 + 3 ^ 40 * 490199 * 2
def baseEnd_490199 : Nat := 18645015063217246508009

theorem tailTrace_490199 : CollatzResearch.WordTrace tailWord_490199 prefixEnd_490199 18645015063217246508009 := by
  unfold tailWord_490199
  simp only [CollatzResearch.WordTrace]
  refine ⟨17879026351100217169073651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11919350900733478112715767 17879026351100217169073651)
  ·
    refine ⟨26818539526650325753610477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17879026351100217169073651 26818539526650325753610477)
    ·
      refine ⟨10056952322493872157603929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26818539526650325753610477 10056952322493872157603929)
      ·
        refine ⟨7542714241870404118202947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10056952322493872157603929 7542714241870404118202947)
        ·
          refine ⟨11314071362805606177304421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7542714241870404118202947 11314071362805606177304421)
          ·
            refine ⟨2121388380526051158244579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11314071362805606177304421 2121388380526051158244579)
            ·
              refine ⟨3182082570789076737366869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2121388380526051158244579 3182082570789076737366869)
              ·
                refine ⟨18645015063217246508009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3182082570789076737366869 18645015063217246508009)
                ·
                  rfl

theorem cell22_490199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 9].length) (baseStart_490199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_490199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_490199 prefixEnd_490199 := by exact prefixLift 490199
  have htrace : WordTrace (prefixWord ++ tailWord_490199) baseStart_490199 baseEnd_490199 := by
    simpa [prefixWord, tailWord_490199, baseEnd_490199] using wordTrace_append hprefix tailTrace_490199
  have hstable : (prefixWord ++ tailWord_490199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490199).length < 2 ^ (prefixWord ++ tailWord_490199).sum := by decide
  have hdescent : baseEnd_490199 < baseStart_490199 := by decide
  rcases family_descends (prefixWord ++ tailWord_490199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490261 : List Nat := [1, 3, 2, 1, 2, 2, 1, 5, 5]
def baseStart_490261 : Nat := 118140960795 + 490261 * 2 ^ 59
def prefixEnd_490261 : Nat := 4983230072969 + 3 ^ 40 * 490261 * 2
def baseEnd_490261 : Nat := 55942119812002574507297

theorem tailTrace_490261 : CollatzResearch.WordTrace tailWord_490261 prefixEnd_490261 55942119812002574507297 := by
  unfold tailWord_490261
  simp only [CollatzResearch.WordTrace]
  refine ⟨17881287676875601757830637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11920858451250401171887091 17881287676875601757830637)
  ·
    refine ⟨6705482878828350659186489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17881287676875601757830637 6705482878828350659186489)
    ·
      refine ⟨5029112159121262994389867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6705482878828350659186489 5029112159121262994389867)
      ·
        refine ⟨7543668238681894491584801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5029112159121262994389867 7543668238681894491584801)
        ·
          refine ⟨5657751179011420868688601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7543668238681894491584801 5657751179011420868688601)
          ·
            refine ⟨4243313384258565651516451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5657751179011420868688601 4243313384258565651516451)
            ·
              refine ⟨6364970076387848477274677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4243313384258565651516451 6364970076387848477274677)
              ·
                refine ⟨596715944661360794744501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6364970076387848477274677 596715944661360794744501)
                ·
                  refine ⟨55942119812002574507297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 596715944661360794744501 55942119812002574507297)
                  ·
                    rfl

theorem cell22_490261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 5, 5].length) (baseStart_490261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_490261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_490261 prefixEnd_490261 := by exact prefixLift 490261
  have htrace : WordTrace (prefixWord ++ tailWord_490261) baseStart_490261 baseEnd_490261 := by
    simpa [prefixWord, tailWord_490261, baseEnd_490261] using wordTrace_append hprefix tailTrace_490261
  have hstable : (prefixWord ++ tailWord_490261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490261).length < 2 ^ (prefixWord ++ tailWord_490261).sum := by decide
  have hdescent : baseEnd_490261 < baseStart_490261 := by decide
  rcases family_descends (prefixWord ++ tailWord_490261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490336 : List Nat := [2, 1, 1, 3, 3, 1, 1, 3, 1, 6]
def baseStart_490336 : Nat := 118140960795 + 490336 * 2 ^ 59
def prefixEnd_490336 : Nat := 4983230072969 + 3 ^ 40 * 490336 * 2
def baseEnd_490336 : Nat := 167852033468732527896661

theorem tailTrace_490336 : CollatzResearch.WordTrace tailWord_490336 prefixEnd_490336 167852033468732527896661 := by
  unfold tailWord_490336
  simp only [CollatzResearch.WordTrace]
  refine ⟨8942011575801944783405431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11922682101069259711207241 8942011575801944783405431)
  ·
    refine ⟨13413017363702917175108147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8942011575801944783405431 13413017363702917175108147)
    ·
      refine ⟨20119526045554375762662221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13413017363702917175108147 20119526045554375762662221)
      ·
        refine ⟨7544822267082890910998333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20119526045554375762662221 7544822267082890910998333)
        ·
          refine ⟨2829308350156084091624375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7544822267082890910998333 2829308350156084091624375)
          ·
            refine ⟨4243962525234126137436563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2829308350156084091624375 4243962525234126137436563)
            ·
              refine ⟨6365943787851189206154845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4243962525234126137436563 6365943787851189206154845)
              ·
                refine ⟨2387228920444195952308067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6365943787851189206154845 2387228920444195952308067)
                ·
                  refine ⟨3580843380666293928462101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2387228920444195952308067 3580843380666293928462101)
                  ·
                    refine ⟨167852033468732527896661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3580843380666293928462101 167852033468732527896661)
                    ·
                      rfl

theorem cell22_490336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 1, 6].length) (baseStart_490336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_490336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_490336 prefixEnd_490336 := by exact prefixLift 490336
  have htrace : WordTrace (prefixWord ++ tailWord_490336) baseStart_490336 baseEnd_490336 := by
    simpa [prefixWord, tailWord_490336, baseEnd_490336] using wordTrace_append hprefix tailTrace_490336
  have hstable : (prefixWord ++ tailWord_490336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490336).length < 2 ^ (prefixWord ++ tailWord_490336).sum := by decide
  have hdescent : baseEnd_490336 < baseStart_490336 := by decide
  rcases family_descends (prefixWord ++ tailWord_490336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490340 : List Nat := [2, 3, 1, 1, 4, 1, 3, 3, 4]
def baseStart_490340 : Nat := 118140960795 + 490340 * 2 ^ 59
def prefixEnd_490340 : Nat := 4983230072969 + 3 ^ 40 * 490340 * 2
def baseEnd_490340 : Nat := 55951134250159283598883

theorem tailTrace_490340 : CollatzResearch.WordTrace tailWord_490340 prefixEnd_490340 55951134250159283598883 := by
  unfold tailWord_490340
  simp only [CollatzResearch.WordTrace]
  refine ⟨8942084521794699124978237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11922779362392932166637649 8942084521794699124978237)
  ·
    refine ⟨3353281695673012171866839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8942084521794699124978237 3353281695673012171866839)
    ·
      refine ⟨5029922543509518257800259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3353281695673012171866839 5029922543509518257800259)
      ·
        refine ⟨7544883815264277386700389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5029922543509518257800259 7544883815264277386700389)
        ·
          refine ⟨1414665715362052010006323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7544883815264277386700389 1414665715362052010006323)
          ·
            refine ⟨2121998573043078015009485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1414665715362052010006323 2121998573043078015009485)
            ·
              refine ⟨795749464891154255628557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2121998573043078015009485 795749464891154255628557)
              ·
                refine ⟨298406049334182845860709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 795749464891154255628557 298406049334182845860709)
                ·
                  refine ⟨55951134250159283598883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 298406049334182845860709 55951134250159283598883)
                  ·
                    rfl

theorem cell22_490340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 3, 4].length) (baseStart_490340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_490340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_490340 prefixEnd_490340 := by exact prefixLift 490340
  have htrace : WordTrace (prefixWord ++ tailWord_490340) baseStart_490340 baseEnd_490340 := by
    simpa [prefixWord, tailWord_490340, baseEnd_490340] using wordTrace_append hprefix tailTrace_490340
  have hstable : (prefixWord ++ tailWord_490340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490340).length < 2 ^ (prefixWord ++ tailWord_490340).sum := by decide
  have hdescent : baseEnd_490340 < baseStart_490340 := by decide
  rcases family_descends (prefixWord ++ tailWord_490340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490353 : List Nat := [1, 2, 2, 2, 1, 5, 1, 2, 2, 4]
def baseStart_490353 : Nat := 118140960795 + 490353 * 2 ^ 59
def prefixEnd_490353 : Nat := 4983230072969 + 3 ^ 40 * 490353 * 2
def baseEnd_490353 : Nat := 167857852916150150221609

theorem tailTrace_490353 : CollatzResearch.WordTrace tailWord_490353 prefixEnd_490353 167857852916150150221609 := by
  unfold tailWord_490353
  simp only [CollatzResearch.WordTrace]
  refine ⟨17884643192542301470179713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11923095461694867646786475 17884643192542301470179713)
  ·
    refine ⟨13413482394406726102634785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17884643192542301470179713 13413482394406726102634785)
    ·
      refine ⟨10060111795805044576976089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13413482394406726102634785 10060111795805044576976089)
      ·
        refine ⟨7545083846853783432732067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10060111795805044576976089 7545083846853783432732067)
        ·
          refine ⟨11317625770280675149098101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7545083846853783432732067 11317625770280675149098101)
          ·
            refine ⟨1061027415963813295227947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11317625770280675149098101 1061027415963813295227947)
            ·
              refine ⟨1591541123945719942841921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1061027415963813295227947 1591541123945719942841921)
              ·
                refine ⟨1193655842959289957131441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1591541123945719942841921 1193655842959289957131441)
                ·
                  refine ⟨895241882219467467848581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1193655842959289957131441 895241882219467467848581)
                  ·
                    refine ⟨167857852916150150221609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 895241882219467467848581 167857852916150150221609)
                    ·
                      rfl

theorem cell22_490353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 2, 2, 4].length) (baseStart_490353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_490353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_490353 prefixEnd_490353 := by exact prefixLift 490353
  have htrace : WordTrace (prefixWord ++ tailWord_490353) baseStart_490353 baseEnd_490353 := by
    simpa [prefixWord, tailWord_490353, baseEnd_490353] using wordTrace_append hprefix tailTrace_490353
  have hstable : (prefixWord ++ tailWord_490353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490353).length < 2 ^ (prefixWord ++ tailWord_490353).sum := by decide
  have hdescent : baseEnd_490353 < baseStart_490353 := by decide
  rcases family_descends (prefixWord ++ tailWord_490353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490357 : List Nat := [1, 3, 4, 1, 1, 3, 3, 2, 4]
def baseStart_490357 : Nat := 118140960795 + 490357 * 2 ^ 59
def prefixEnd_490357 : Nat := 4983230072969 + 3 ^ 40 * 490357 * 2
def baseEnd_490357 : Nat := 55953074065965157707199

theorem tailTrace_490357 : CollatzResearch.WordTrace tailWord_490357 prefixEnd_490357 55953074065965157707199 := by
  unfold tailWord_490357
  simp only [CollatzResearch.WordTrace]
  refine ⟨17884789084527810153325325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11923192723018540102216883 17884789084527810153325325)
  ·
    refine ⟨6706795906697928807496997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17884789084527810153325325 6706795906697928807496997)
    ·
      refine ⟨1257524232505861651405687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6706795906697928807496997 1257524232505861651405687)
      ·
        refine ⟨1886286348758792477108531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1257524232505861651405687 1886286348758792477108531)
        ·
          refine ⟨2829429523138188715662797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1886286348758792477108531 2829429523138188715662797)
          ·
            refine ⟨1061036071176820768373549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2829429523138188715662797 1061036071176820768373549)
            ·
              refine ⟨397888526691307788140081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1061036071176820768373549 397888526691307788140081)
              ·
                refine ⟨298416395018480841105061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 397888526691307788140081 298416395018480841105061)
                ·
                  refine ⟨55953074065965157707199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 298416395018480841105061 55953074065965157707199)
                  ·
                    rfl

theorem cell22_490357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 3, 2, 4].length) (baseStart_490357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_490357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_490357 prefixEnd_490357 := by exact prefixLift 490357
  have htrace : WordTrace (prefixWord ++ tailWord_490357) baseStart_490357 baseEnd_490357 := by
    simpa [prefixWord, tailWord_490357, baseEnd_490357] using wordTrace_append hprefix tailTrace_490357
  have hstable : (prefixWord ++ tailWord_490357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490357).length < 2 ^ (prefixWord ++ tailWord_490357).sum := by decide
  have hdescent : baseEnd_490357 < baseStart_490357 := by decide
  rcases family_descends (prefixWord ++ tailWord_490357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490411 : List Nat := [1, 1, 1, 1, 2, 1, 1, 5, 4, 5]
def baseStart_490411 : Nat := 118140960795 + 490411 * 2 ^ 59
def prefixEnd_490411 : Nat := 4983230072969 + 3 ^ 40 * 490411 * 2
def baseEnd_490411 : Nat := 167877707501457332271431

theorem tailTrace_490411 : CollatzResearch.WordTrace tailWord_490411 prefixEnd_490411 167877707501457332271431 := by
  unfold tailWord_490411
  simp only [CollatzResearch.WordTrace]
  refine ⟨17886758626332177375791087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11924505750888118250527391 17886758626332177375791087)
  ·
    refine ⟨26830137939498266063686631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17886758626332177375791087 26830137939498266063686631)
    ·
      refine ⟨40245206909247399095529947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26830137939498266063686631 40245206909247399095529947)
      ·
        refine ⟨60367810363871098643294921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40245206909247399095529947 60367810363871098643294921)
        ·
          refine ⟨45275857772903323982471191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60367810363871098643294921 45275857772903323982471191)
          ·
            refine ⟨67913786659354985973706787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45275857772903323982471191 67913786659354985973706787)
            ·
              refine ⟨101870679989032478960560181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67913786659354985973706787 101870679989032478960560181)
              ·
                refine ⟨9550376248971794902552517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101870679989032478960560181 9550376248971794902552517)
                ·
                  refine ⟨1790695546682211544228597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9550376248971794902552517 1790695546682211544228597)
                  ·
                    refine ⟨167877707501457332271431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1790695546682211544228597 167877707501457332271431)
                    ·
                      rfl

theorem cell22_490411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 4, 5].length) (baseStart_490411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_490411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_490411 prefixEnd_490411 := by exact prefixLift 490411
  have htrace : WordTrace (prefixWord ++ tailWord_490411) baseStart_490411 baseEnd_490411 := by
    simpa [prefixWord, tailWord_490411, baseEnd_490411] using wordTrace_append hprefix tailTrace_490411
  have hstable : (prefixWord ++ tailWord_490411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490411).length < 2 ^ (prefixWord ++ tailWord_490411).sum := by decide
  have hdescent : baseEnd_490411 < baseStart_490411 := by decide
  rcases family_descends (prefixWord ++ tailWord_490411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490438 : List Nat := [6, 1, 3, 1, 1, 2, 1, 1, 2, 4]
def baseStart_490438 : Nat := 118140960795 + 490438 * 2 ^ 59
def prefixEnd_490438 : Nat := 4983230072969 + 3 ^ 40 * 490438 * 2
def baseEnd_490438 : Nat := 167886950153238261846349

theorem tailTrace_490438 : CollatzResearch.WordTrace tailWord_490438 prefixEnd_490438 167886950153238261846349 := by
  unfold tailWord_490438
  simp only [CollatzResearch.WordTrace]
  refine ⟨558991981163573780844499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11925162264822907324682645 558991981163573780844499)
  ·
    refine ⟨838487971745360671266749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 558991981163573780844499 838487971745360671266749)
    ·
      refine ⟨314432989404510251725031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 838487971745360671266749 314432989404510251725031)
      ·
        refine ⟨471649484106765377587547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314432989404510251725031 471649484106765377587547)
        ·
          refine ⟨707474226160148066381321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 471649484106765377587547 707474226160148066381321)
          ·
            refine ⟨530605669620111049785991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 707474226160148066381321 530605669620111049785991)
            ·
              refine ⟨795908504430166574678987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 530605669620111049785991 795908504430166574678987)
              ·
                refine ⟨1193862756645249862018481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 795908504430166574678987 1193862756645249862018481)
                ·
                  refine ⟨895397067483937396513861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1193862756645249862018481 895397067483937396513861)
                  ·
                    refine ⟨167886950153238261846349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 895397067483937396513861 167886950153238261846349)
                    ·
                      rfl

theorem cell22_490438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_490438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_490438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_490438 prefixEnd_490438 := by exact prefixLift 490438
  have htrace : WordTrace (prefixWord ++ tailWord_490438) baseStart_490438 baseEnd_490438 := by
    simpa [prefixWord, tailWord_490438, baseEnd_490438] using wordTrace_append hprefix tailTrace_490438
  have hstable : (prefixWord ++ tailWord_490438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490438).length < 2 ^ (prefixWord ++ tailWord_490438).sum := by decide
  have hdescent : baseEnd_490438 < baseStart_490438 := by decide
  rcases family_descends (prefixWord ++ tailWord_490438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490443 : List Nat := [1, 1, 1, 1, 3, 5, 2, 1, 3, 4]
def baseStart_490443 : Nat := 118140960795 + 490443 * 2 ^ 59
def prefixEnd_490443 : Nat := 4983230072969 + 3 ^ 40 * 490443 * 2
def baseEnd_490443 : Nat := 167888661755419915471333

theorem tailTrace_490443 : CollatzResearch.WordTrace tailWord_490443 prefixEnd_490443 167888661755419915471333 := by
  unfold tailWord_490443
  simp only [CollatzResearch.WordTrace]
  refine ⟨17887925762216246840955983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11925283841477497893970655 17887925762216246840955983)
  ·
    refine ⟨26831888643324370261433975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17887925762216246840955983 26831888643324370261433975)
    ·
      refine ⟨40247832964986555392150963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26831888643324370261433975 40247832964986555392150963)
      ·
        refine ⟨60371749447479833088226445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40247832964986555392150963 60371749447479833088226445)
        ·
          refine ⟨22639406042804937408084917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60371749447479833088226445 22639406042804937408084917)
          ·
            refine ⟨2122444316512962882007961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22639406042804937408084917 2122444316512962882007961)
            ·
              refine ⟨1591833237384722161505971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2122444316512962882007961 1591833237384722161505971)
              ·
                refine ⟨2387749856077083242258957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1591833237384722161505971 2387749856077083242258957)
                ·
                  refine ⟨895406196028906215847109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2387749856077083242258957 895406196028906215847109)
                  ·
                    refine ⟨167888661755419915471333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 895406196028906215847109 167888661755419915471333)
                    ·
                      rfl

theorem cell22_490443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 3, 4].length) (baseStart_490443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_490443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_490443 prefixEnd_490443 := by exact prefixLift 490443
  have htrace : WordTrace (prefixWord ++ tailWord_490443) baseStart_490443 baseEnd_490443 := by
    simpa [prefixWord, tailWord_490443, baseEnd_490443] using wordTrace_append hprefix tailTrace_490443
  have hstable : (prefixWord ++ tailWord_490443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490443).length < 2 ^ (prefixWord ++ tailWord_490443).sum := by decide
  have hdescent : baseEnd_490443 < baseStart_490443 := by decide
  rcases family_descends (prefixWord ++ tailWord_490443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490490 : List Nat := [3, 1, 1, 1, 1, 2, 1, 7, 2, 3]
def baseStart_490490 : Nat := 118140960795 + 490490 * 2 ^ 59
def prefixEnd_490490 : Nat := 4983230072969 + 3 ^ 40 * 490490 * 2
def baseEnd_490490 : Nat := 167904750815927459546189

theorem tailTrace_490490 : CollatzResearch.WordTrace tailWord_490490 prefixEnd_490490 167904750815927459546189 := by
  unfold tailWord_490490
  simp only [CollatzResearch.WordTrace]
  refine ⟨4472409998261493466979231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11926426662030649245277949 4472409998261493466979231)
  ·
    refine ⟨6708614997392240200468847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4472409998261493466979231 6708614997392240200468847)
    ·
      refine ⟨10062922496088360300703271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6708614997392240200468847 10062922496088360300703271)
      ·
        refine ⟨15094383744132540451054907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10062922496088360300703271 15094383744132540451054907)
        ·
          refine ⟨22641575616198810676582361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15094383744132540451054907 22641575616198810676582361)
          ·
            refine ⟨16981181712149108007436771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22641575616198810676582361 16981181712149108007436771)
            ·
              refine ⟨25471772568223662011155157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16981181712149108007436771 25471772568223662011155157)
              ·
                refine ⟨596994669567742078386449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 25471772568223662011155157 596994669567742078386449)
                ·
                  refine ⟨447746002175806558789837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 596994669567742078386449 447746002175806558789837)
                  ·
                    refine ⟨167904750815927459546189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 447746002175806558789837 167904750815927459546189)
                    ·
                      rfl

theorem cell22_490490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 7, 2, 3].length) (baseStart_490490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_490490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_490490 prefixEnd_490490 := by exact prefixLift 490490
  have htrace : WordTrace (prefixWord ++ tailWord_490490) baseStart_490490 baseEnd_490490 := by
    simpa [prefixWord, tailWord_490490, baseEnd_490490] using wordTrace_append hprefix tailTrace_490490
  have hstable : (prefixWord ++ tailWord_490490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490490).length < 2 ^ (prefixWord ++ tailWord_490490).sum := by decide
  have hdescent : baseEnd_490490 < baseStart_490490 := by decide
  rcases family_descends (prefixWord ++ tailWord_490490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490494 : List Nat := [4, 2, 2, 2, 2, 1, 2, 2, 1, 4]
def baseStart_490494 : Nat := 118140960795 + 490494 * 2 ^ 59
def prefixEnd_490494 : Nat := 4983230072969 + 3 ^ 40 * 490494 * 2
def baseEnd_490494 : Nat := 167906120097672782446177

theorem tailTrace_490494 : CollatzResearch.WordTrace tailWord_490494 prefixEnd_490494 167906120097672782446177 := by
  unfold tailWord_490494
  simp only [CollatzResearch.WordTrace]
  refine ⟨2236223235628935318882817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11926523923354321700708357 2236223235628935318882817)
  ·
    refine ⟨1677167426721701489162113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2236223235628935318882817 1677167426721701489162113)
    ·
      refine ⟨1257875570041276116871585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1677167426721701489162113 1257875570041276116871585)
      ·
        refine ⟨943406677530957087653689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1257875570041276116871585 943406677530957087653689)
        ·
          refine ⟨707555008148217815740267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 943406677530957087653689 707555008148217815740267)
          ·
            refine ⟨1061332512222326723610401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 707555008148217815740267 1061332512222326723610401)
            ·
              refine ⟨795999384166745042707801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1061332512222326723610401 795999384166745042707801)
              ·
                refine ⟨596999538125058782030851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 795999384166745042707801 596999538125058782030851)
                ·
                  refine ⟨895499307187588173046277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 596999538125058782030851 895499307187588173046277)
                  ·
                    refine ⟨167906120097672782446177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 895499307187588173046277 167906120097672782446177)
                    ·
                      rfl

theorem cell22_490494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_490494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_490494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_490494 prefixEnd_490494 := by exact prefixLift 490494
  have htrace : WordTrace (prefixWord ++ tailWord_490494) baseStart_490494 baseEnd_490494 := by
    simpa [prefixWord, tailWord_490494, baseEnd_490494] using wordTrace_append hprefix tailTrace_490494
  have hstable : (prefixWord ++ tailWord_490494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490494).length < 2 ^ (prefixWord ++ tailWord_490494).sum := by decide
  have hdescent : baseEnd_490494 < baseStart_490494 := by decide
  rcases family_descends (prefixWord ++ tailWord_490494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490503 : List Nat := [1, 1, 4, 3, 1, 1, 3, 8]
def baseStart_490503 : Nat := 118140960795 + 490503 * 2 ^ 59
def prefixEnd_490503 : Nat := 4983230072969 + 3 ^ 40 * 490503 * 2
def baseEnd_490503 : Nat := 18656577886844417663461

theorem tailTrace_490503 : CollatzResearch.WordTrace tailWord_490503 prefixEnd_490503 18656577886844417663461 := by
  unfold tailWord_490503
  simp only [CollatzResearch.WordTrace]
  refine ⟨17890114141998877088140163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11926742761332584725426775 17890114141998877088140163)
  ·
    refine ⟨26835171212998315632210245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17890114141998877088140163 26835171212998315632210245)
    ·
      refine ⟨5031594602437184181039421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26835171212998315632210245 5031594602437184181039421)
      ·
        refine ⟨1886847975913944067889783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5031594602437184181039421 1886847975913944067889783)
        ·
          refine ⟨2830271963870916101834675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1886847975913944067889783 2830271963870916101834675)
          ·
            refine ⟨4245407945806374152752013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2830271963870916101834675 4245407945806374152752013)
            ·
              refine ⟨1592027979677390307282005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4245407945806374152752013 1592027979677390307282005)
              ·
                refine ⟨18656577886844417663461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1592027979677390307282005 18656577886844417663461)
                ·
                  rfl

theorem cell22_490503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 8].length) (baseStart_490503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_490503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_490503 prefixEnd_490503 := by exact prefixLift 490503
  have htrace : WordTrace (prefixWord ++ tailWord_490503) baseStart_490503 baseEnd_490503 := by
    simpa [prefixWord, tailWord_490503, baseEnd_490503] using wordTrace_append hprefix tailTrace_490503
  have hstable : (prefixWord ++ tailWord_490503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490503).length < 2 ^ (prefixWord ++ tailWord_490503).sum := by decide
  have hdescent : baseEnd_490503 < baseStart_490503 := by decide
  rcases family_descends (prefixWord ++ tailWord_490503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490533 : List Nat := [1, 3, 1, 2, 2, 2, 2, 1, 2, 6]
def baseStart_490533 : Nat := 118140960795 + 490533 * 2 ^ 59
def prefixEnd_490533 : Nat := 4983230072969 + 3 ^ 40 * 490533 * 2
def baseEnd_490533 : Nat := 167919470594689680721057

theorem tailTrace_490533 : CollatzResearch.WordTrace tailWord_490533 prefixEnd_490533 167919470594689680721057 := by
  unfold tailWord_490533
  simp only [CollatzResearch.WordTrace]
  refine ⟨17891208331890192211732253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11927472221260128141154835 17891208331890192211732253)
  ·
    refine ⟨6709203124458822079399595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17891208331890192211732253 6709203124458822079399595)
    ·
      refine ⟨10063804686688233119099393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6709203124458822079399595 10063804686688233119099393)
      ·
        refine ⟨7547853515016174839324545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10063804686688233119099393 7547853515016174839324545)
        ·
          refine ⟨5660890136262131129493409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7547853515016174839324545 5660890136262131129493409)
          ·
            refine ⟨4245667602196598347120057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5660890136262131129493409 4245667602196598347120057)
            ·
              refine ⟨3184250701647448760340043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4245667602196598347120057 3184250701647448760340043)
              ·
                refine ⟨4776376052471173140510065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3184250701647448760340043 4776376052471173140510065)
                ·
                  refine ⟨3582282039353379855382549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4776376052471173140510065 3582282039353379855382549)
                  ·
                    refine ⟨167919470594689680721057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3582282039353379855382549 167919470594689680721057)
                    ·
                      rfl

theorem cell22_490533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 6].length) (baseStart_490533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_490533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_490533 prefixEnd_490533 := by exact prefixLift 490533
  have htrace : WordTrace (prefixWord ++ tailWord_490533) baseStart_490533 baseEnd_490533 := by
    simpa [prefixWord, tailWord_490533, baseEnd_490533] using wordTrace_append hprefix tailTrace_490533
  have hstable : (prefixWord ++ tailWord_490533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490533).length < 2 ^ (prefixWord ++ tailWord_490533).sum := by decide
  have hdescent : baseEnd_490533 < baseStart_490533 := by decide
  rcases family_descends (prefixWord ++ tailWord_490533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490610 : List Nat := [3, 2, 1, 2, 2, 1, 3, 2, 6]
def baseStart_490610 : Nat := 118140960795 + 490610 * 2 ^ 59
def prefixEnd_490610 : Nat := 4983230072969 + 3 ^ 40 * 490610 * 2
def baseEnd_490610 : Nat := 55981943089429048848607

theorem tailTrace_490610 : CollatzResearch.WordTrace tailWord_490610 prefixEnd_490610 55981943089429048848607 := by
  unfold tailWord_490610
  simp only [CollatzResearch.WordTrace]
  refine ⟨4473504188152808590571321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11929344501740822908190189 4473504188152808590571321)
  ·
    refine ⟨3355128141114606442928491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4473504188152808590571321 3355128141114606442928491)
    ·
      refine ⟨5032692211671909664392737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3355128141114606442928491 5032692211671909664392737)
      ·
        refine ⟨3774519158753932248294553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5032692211671909664392737 3774519158753932248294553)
        ·
          refine ⟨2830889369065449186220915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3774519158753932248294553 2830889369065449186220915)
          ·
            refine ⟨4246334053598173779331373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2830889369065449186220915 4246334053598173779331373)
            ·
              refine ⟨1592375270099315167249265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4246334053598173779331373 1592375270099315167249265)
              ·
                refine ⟨1194281452574486375436949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1592375270099315167249265 1194281452574486375436949)
                ·
                  refine ⟨55981943089429048848607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1194281452574486375436949 55981943089429048848607)
                  ·
                    rfl

theorem cell22_490610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 2, 6].length) (baseStart_490610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_490610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_490610 prefixEnd_490610 := by exact prefixLift 490610
  have htrace : WordTrace (prefixWord ++ tailWord_490610) baseStart_490610 baseEnd_490610 := by
    simpa [prefixWord, tailWord_490610, baseEnd_490610] using wordTrace_append hprefix tailTrace_490610
  have hstable : (prefixWord ++ tailWord_490610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490610).length < 2 ^ (prefixWord ++ tailWord_490610).sum := by decide
  have hdescent : baseEnd_490610 < baseStart_490610 := by decide
  rcases family_descends (prefixWord ++ tailWord_490610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490627 : List Nat := [1, 1, 1, 3, 3, 2, 4, 3, 4]
def baseStart_490627 : Nat := 118140960795 + 490627 * 2 ^ 59
def prefixEnd_490627 : Nat := 4983230072969 + 3 ^ 40 * 490627 * 2
def baseEnd_490627 : Nat := 55983882905234922956923

theorem tailTrace_490627 : CollatzResearch.WordTrace tailWord_490627 prefixEnd_490627 55983882905234922956923 := by
  unfold tailWord_490627
  simp only [CollatzResearch.WordTrace]
  refine ⟨17894636793549646265654135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11929757862366430843769423 17894636793549646265654135)
  ·
    refine ⟨26841955190324469398481203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17894636793549646265654135 26841955190324469398481203)
    ·
      refine ⟨40262932785486704097721805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26841955190324469398481203 40262932785486704097721805)
      ·
        refine ⟨15098599794557514036645677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40262932785486704097721805 15098599794557514036645677)
        ·
          refine ⟨5661974922959067763742129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15098599794557514036645677 5661974922959067763742129)
          ·
            refine ⟨4246481192219300822806597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5661974922959067763742129 4246481192219300822806597)
            ·
              refine ⟨796215223541118904276237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4246481192219300822806597 796215223541118904276237)
              ·
                refine ⟨298580708827919589103589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 796215223541118904276237 298580708827919589103589)
                ·
                  refine ⟨55983882905234922956923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 298580708827919589103589 55983882905234922956923)
                  ·
                    rfl

theorem cell22_490627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 3, 4].length) (baseStart_490627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_490627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_490627 prefixEnd_490627 := by exact prefixLift 490627
  have htrace : WordTrace (prefixWord ++ tailWord_490627) baseStart_490627 baseEnd_490627 := by
    simpa [prefixWord, tailWord_490627, baseEnd_490627] using wordTrace_append hprefix tailTrace_490627
  have hstable : (prefixWord ++ tailWord_490627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490627).length < 2 ^ (prefixWord ++ tailWord_490627).sum := by decide
  have hdescent : baseEnd_490627 < baseStart_490627 := by decide
  rcases family_descends (prefixWord ++ tailWord_490627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490710 : List Nat := [5, 2, 1, 2, 2, 2, 2, 1, 2, 3]
def baseStart_490710 : Nat := 118140960795 + 490710 * 2 ^ 59
def prefixEnd_490710 : Nat := 4983230072969 + 3 ^ 40 * 490710 * 2
def baseEnd_490710 : Nat := 167980061311920219045515

theorem tailTrace_490710 : CollatzResearch.WordTrace tailWord_490710 prefixEnd_490710 167980061311920219045515 := by
  unfold tailWord_490710
  simp only [CollatzResearch.WordTrace]
  refine ⟨1118604003265559465057849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11931776034832634293950389 1118604003265559465057849)
  ·
    refine ⟨838953002449169598793387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1118604003265559465057849 838953002449169598793387)
    ·
      refine ⟨1258429503673754398190081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 838953002449169598793387 1258429503673754398190081)
      ·
        refine ⟨943822127755315798642561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1258429503673754398190081 943822127755315798642561)
        ·
          refine ⟨707866595816486848981921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 943822127755315798642561 707866595816486848981921)
          ·
            refine ⟨530899946862365136736441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 707866595816486848981921 530899946862365136736441)
            ·
              refine ⟨398174960146773852552331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 530899946862365136736441 398174960146773852552331)
              ·
                refine ⟨597262440220160778828497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 398174960146773852552331 597262440220160778828497)
                ·
                  refine ⟨447946830165120584121373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 597262440220160778828497 447946830165120584121373)
                  ·
                    refine ⟨167980061311920219045515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 447946830165120584121373 167980061311920219045515)
                    ·
                      rfl

theorem cell22_490710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_490710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_490710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_490710 prefixEnd_490710 := by exact prefixLift 490710
  have htrace : WordTrace (prefixWord ++ tailWord_490710) baseStart_490710 baseEnd_490710 := by
    simpa [prefixWord, tailWord_490710, baseEnd_490710] using wordTrace_append hprefix tailTrace_490710
  have hstable : (prefixWord ++ tailWord_490710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490710).length < 2 ^ (prefixWord ++ tailWord_490710).sum := by decide
  have hdescent : baseEnd_490710 < baseStart_490710 := by decide
  rcases family_descends (prefixWord ++ tailWord_490710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490794 : List Nat := [3, 1, 4, 2, 1, 1, 2, 2, 1, 5]
def baseStart_490794 : Nat := 118140960795 + 490794 * 2 ^ 59
def prefixEnd_490794 : Nat := 4983230072969 + 3 ^ 40 * 490794 * 2
def baseEnd_490794 : Nat := 168008816228571999945257

theorem tailTrace_490794 : CollatzResearch.WordTrace tailWord_490794 prefixEnd_490794 168008816228571999945257 := by
  unfold tailWord_490794
  simp only [CollatzResearch.WordTrace]
  refine ⟨4475181945986158446745859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11933818522629755857988957 4475181945986158446745859)
  ·
    refine ⟨6712772918979237670118789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4475181945986158446745859 6712772918979237670118789)
    ·
      refine ⟨1258644922308607063147273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6712772918979237670118789 1258644922308607063147273)
      ·
        refine ⟨943983691731455297360455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1258644922308607063147273 943983691731455297360455)
        ·
          refine ⟨1415975537597182946040683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 943983691731455297360455 1415975537597182946040683)
          ·
            refine ⟨2123963306395774419061025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1415975537597182946040683 2123963306395774419061025)
            ·
              refine ⟨1592972479796830814295769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2123963306395774419061025 1592972479796830814295769)
              ·
                refine ⟨1194729359847623110721827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1592972479796830814295769 1194729359847623110721827)
                ·
                  refine ⟨1792094039771434666082741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1194729359847623110721827 1792094039771434666082741)
                  ·
                    refine ⟨168008816228571999945257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1792094039771434666082741 168008816228571999945257)
                    ·
                      rfl

theorem cell22_490794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_490794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_490794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_490794 prefixEnd_490794 := by exact prefixLift 490794
  have htrace : WordTrace (prefixWord ++ tailWord_490794) baseStart_490794 baseEnd_490794 := by
    simpa [prefixWord, tailWord_490794, baseEnd_490794] using wordTrace_append hprefix tailTrace_490794
  have hstable : (prefixWord ++ tailWord_490794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490794).length < 2 ^ (prefixWord ++ tailWord_490794).sum := by decide
  have hdescent : baseEnd_490794 < baseStart_490794 := by decide
  rcases family_descends (prefixWord ++ tailWord_490794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490839 : List Nat := [1, 1, 3, 2, 3, 2, 2, 2, 3, 3]
def baseStart_490839 : Nat := 118140960795 + 490839 * 2 ^ 59
def prefixEnd_490839 : Nat := 4983230072969 + 3 ^ 40 * 490839 * 2
def baseEnd_490839 : Nat := 168024220648206882570119

theorem tailTrace_490839 : CollatzResearch.WordTrace tailWord_490839 prefixEnd_490839 168024220648206882570119 := by
  unfold tailWord_490839
  simp only [CollatzResearch.WordTrace]
  refine ⟨17902369068781606472371571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11934912712521070981581047 17902369068781606472371571)
  ·
    refine ⟨26853553603172409708557357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17902369068781606472371571 26853553603172409708557357)
    ·
      refine ⟨10070082601189653640709009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26853553603172409708557357 10070082601189653640709009)
      ·
        refine ⟨7552561950892240230531757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10070082601189653640709009 7552561950892240230531757)
        ·
          refine ⟨2832210731584590086449409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7552561950892240230531757 2832210731584590086449409)
          ·
            refine ⟨2124158048688442564837057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2832210731584590086449409 2124158048688442564837057)
            ·
              refine ⟨1593118536516331923627793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2124158048688442564837057 1593118536516331923627793)
              ·
                refine ⟨1194838902387248942720845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1593118536516331923627793 1194838902387248942720845)
                ·
                  refine ⟨448064588395218353520317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1194838902387248942720845 448064588395218353520317)
                  ·
                    refine ⟨168024220648206882570119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 448064588395218353520317 168024220648206882570119)
                    ·
                      rfl

theorem cell22_490839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 2, 3, 3].length) (baseStart_490839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_490839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_490839 prefixEnd_490839 := by exact prefixLift 490839
  have htrace : WordTrace (prefixWord ++ tailWord_490839) baseStart_490839 baseEnd_490839 := by
    simpa [prefixWord, tailWord_490839, baseEnd_490839] using wordTrace_append hprefix tailTrace_490839
  have hstable : (prefixWord ++ tailWord_490839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490839).length < 2 ^ (prefixWord ++ tailWord_490839).sum := by decide
  have hdescent : baseEnd_490839 < baseStart_490839 := by decide
  rcases family_descends (prefixWord ++ tailWord_490839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490852 : List Nat := [2, 3, 1, 1, 3, 2, 1, 2, 7]
def baseStart_490852 : Nat := 118140960795 + 490852 * 2 ^ 59
def prefixEnd_490852 : Nat := 4983230072969 + 3 ^ 40 * 490852 * 2
def baseEnd_490852 : Nat := 56009556937959727331693

theorem tailTrace_490852 : CollatzResearch.WordTrace tailWord_490852 prefixEnd_490852 56009556937959727331693 := by
  unfold tailWord_490852
  simp only [CollatzResearch.WordTrace]
  refine ⟨8951421608867254846297405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11935228811823006461729873 8951421608867254846297405)
  ·
    refine ⟨3356783103325220567361527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8951421608867254846297405 3356783103325220567361527)
    ·
      refine ⟨5035174654987830851042291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3356783103325220567361527 5035174654987830851042291)
      ·
        refine ⟨7552761982481746276563437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5035174654987830851042291 7552761982481746276563437)
        ·
          refine ⟨2832285743430654853711289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7552761982481746276563437 2832285743430654853711289)
          ·
            refine ⟨2124214307572991140283467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2832285743430654853711289 2124214307572991140283467)
            ·
              refine ⟨3186321461359486710425201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2124214307572991140283467 3186321461359486710425201)
              ·
                refine ⟨2389741096019615032818901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3186321461359486710425201 2389741096019615032818901)
                ·
                  refine ⟨56009556937959727331693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2389741096019615032818901 56009556937959727331693)
                  ·
                    rfl

theorem cell22_490852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 7].length) (baseStart_490852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_490852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_490852 prefixEnd_490852 := by exact prefixLift 490852
  have htrace : WordTrace (prefixWord ++ tailWord_490852) baseStart_490852 baseEnd_490852 := by
    simpa [prefixWord, tailWord_490852, baseEnd_490852] using wordTrace_append hprefix tailTrace_490852
  have hstable : (prefixWord ++ tailWord_490852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490852).length < 2 ^ (prefixWord ++ tailWord_490852).sum := by decide
  have hdescent : baseEnd_490852 < baseStart_490852 := by decide
  rcases family_descends (prefixWord ++ tailWord_490852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491004 : List Nat := [2, 2, 2, 1, 2, 1, 2, 5, 5]
def baseStart_491004 : Nat := 118140960795 + 491004 * 2 ^ 59
def prefixEnd_491004 : Nat := 4983230072969 + 3 ^ 40 * 491004 * 2
def baseEnd_491004 : Nat := 56026901173400484064871

theorem tailTrace_491004 : CollatzResearch.WordTrace tailWord_491004 prefixEnd_491004 56026901173400484064871 := by
  unfold tailWord_491004
  simp only [CollatzResearch.WordTrace]
  refine ⟨8954193556591919826064033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11938924742122559768085377 8954193556591919826064033)
  ·
    refine ⟨6715645167443939869548025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8954193556591919826064033 6715645167443939869548025)
    ·
      refine ⟨5036733875582954902161019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6715645167443939869548025 5036733875582954902161019)
      ·
        refine ⟨7555100813374432353241529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5036733875582954902161019 7555100813374432353241529)
        ·
          refine ⟨5666325610030824264931147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7555100813374432353241529 5666325610030824264931147)
          ·
            refine ⟨8499488415046236397396721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5666325610030824264931147 8499488415046236397396721)
            ·
              refine ⟨6374616311284677298047541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8499488415046236397396721 6374616311284677298047541)
              ·
                refine ⟨597620279182938496691957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6374616311284677298047541 597620279182938496691957)
                ·
                  refine ⟨56026901173400484064871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 597620279182938496691957 56026901173400484064871)
                  ·
                    rfl

theorem cell22_491004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 5, 5].length) (baseStart_491004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_491004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_491004 prefixEnd_491004 := by exact prefixLift 491004
  have htrace : WordTrace (prefixWord ++ tailWord_491004) baseStart_491004 baseEnd_491004 := by
    simpa [prefixWord, tailWord_491004, baseEnd_491004] using wordTrace_append hprefix tailTrace_491004
  have hstable : (prefixWord ++ tailWord_491004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491004).length < 2 ^ (prefixWord ++ tailWord_491004).sum := by decide
  have hdescent : baseEnd_491004 < baseStart_491004 := by decide
  rcases family_descends (prefixWord ++ tailWord_491004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491034 : List Nat := [3, 1, 1, 3, 1, 1, 1, 2, 5, 4]
def baseStart_491034 : Nat := 118140960795 + 491034 * 2 ^ 59
def prefixEnd_491034 : Nat := 4983230072969 + 3 ^ 40 * 491034 * 2
def baseEnd_491034 : Nat := 168090973133291373944521

theorem tailTrace_491034 : CollatzResearch.WordTrace tailWord_491034 prefixEnd_491034 168090973133291373944521 := by
  unfold tailWord_491034
  simp only [CollatzResearch.WordTrace]
  refine ⟨4477370325768788693930039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11939654202050103183813437 4477370325768788693930039)
  ·
    refine ⟨6716055488653183040895059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4477370325768788693930039 6716055488653183040895059)
    ·
      refine ⟨10074083232979774561342589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6716055488653183040895059 10074083232979774561342589)
      ·
        refine ⟨3777781212367415460503471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10074083232979774561342589 3777781212367415460503471)
        ·
          refine ⟨5666671818551123190755207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3777781212367415460503471 5666671818551123190755207)
          ·
            refine ⟨8500007727826684786132811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5666671818551123190755207 8500007727826684786132811)
            ·
              refine ⟨12750011591740027179199217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8500007727826684786132811 12750011591740027179199217)
              ·
                refine ⟨9562508693805020384399413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12750011591740027179199217 9562508693805020384399413)
                ·
                  refine ⟨896485190044220661037445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9562508693805020384399413 896485190044220661037445)
                  ·
                    refine ⟨168090973133291373944521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 896485190044220661037445 168090973133291373944521)
                    ·
                      rfl

theorem cell22_491034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 5, 4].length) (baseStart_491034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_491034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_491034 prefixEnd_491034 := by exact prefixLift 491034
  have htrace : WordTrace (prefixWord ++ tailWord_491034) baseStart_491034 baseEnd_491034 := by
    simpa [prefixWord, tailWord_491034, baseEnd_491034] using wordTrace_append hprefix tailTrace_491034
  have hstable : (prefixWord ++ tailWord_491034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491034).length < 2 ^ (prefixWord ++ tailWord_491034).sum := by decide
  have hdescent : baseEnd_491034 < baseStart_491034 := by decide
  rcases family_descends (prefixWord ++ tailWord_491034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491100 : List Nat := [2, 2, 4, 1, 2, 1, 4, 2, 4]
def baseStart_491100 : Nat := 118140960795 + 491100 * 2 ^ 59
def prefixEnd_491100 : Nat := 4983230072969 + 3 ^ 40 * 491100 * 2
def baseEnd_491100 : Nat := 56037855427363067264773

theorem tailTrace_491100 : CollatzResearch.WordTrace tailWord_491100 prefixEnd_491100 56037855427363067264773 := by
  unfold tailWord_491100
  simp only [CollatzResearch.WordTrace]
  refine ⟨8955944260418024023811377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11941259013890698698415169 8955944260418024023811377)
  ·
    refine ⟨6716958195313518017858533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8955944260418024023811377 6716958195313518017858533)
    ·
      refine ⟨1259429661621284628348475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6716958195313518017858533 1259429661621284628348475)
      ·
        refine ⟨1889144492431926942522713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1259429661621284628348475 1889144492431926942522713)
        ·
          refine ⟨1416858369323945206892035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1889144492431926942522713 1416858369323945206892035)
          ·
            refine ⟨2125287553985917810338053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1416858369323945206892035 2125287553985917810338053)
            ·
              refine ⟨398491416372359589438385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2125287553985917810338053 398491416372359589438385)
              ·
                refine ⟨298868562279269692078789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 398491416372359589438385 298868562279269692078789)
                ·
                  refine ⟨56037855427363067264773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 298868562279269692078789 56037855427363067264773)
                  ·
                    rfl

theorem cell22_491100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 4, 2, 4].length) (baseStart_491100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_491100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_491100 prefixEnd_491100 := by exact prefixLift 491100
  have htrace : WordTrace (prefixWord ++ tailWord_491100) baseStart_491100 baseEnd_491100 := by
    simpa [prefixWord, tailWord_491100, baseEnd_491100] using wordTrace_append hprefix tailTrace_491100
  have hstable : (prefixWord ++ tailWord_491100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491100).length < 2 ^ (prefixWord ++ tailWord_491100).sum := by decide
  have hdescent : baseEnd_491100 < baseStart_491100 := by decide
  rcases family_descends (prefixWord ++ tailWord_491100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491139 : List Nat := [1, 1, 1, 3, 3, 1, 1, 4, 7]
def baseStart_491139 : Nat := 118140960795 + 491139 * 2 ^ 59
def prefixEnd_491139 : Nat := 4983230072969 + 3 ^ 40 * 491139 * 2
def baseEnd_491139 : Nat := 56042305593035366689733

theorem tailTrace_491139 : CollatzResearch.WordTrace tailWord_491139 prefixEnd_491139 56042305593035366689733 := by
  unfold tailWord_491139
  simp only [CollatzResearch.WordTrace]
  refine ⟨17913310967694757708292471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11942207311796505138861647 17913310967694757708292471)
  ·
    refine ⟨26869966451542136562438707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17913310967694757708292471 26869966451542136562438707)
    ·
      refine ⟨40304949677313204843658061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26869966451542136562438707 40304949677313204843658061)
      ·
        refine ⟨15114356128992451816371773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40304949677313204843658061 15114356128992451816371773)
        ·
          refine ⟨5667883548372169431139415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15114356128992451816371773 5667883548372169431139415)
          ·
            refine ⟨8501825322558254146709123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5667883548372169431139415 8501825322558254146709123)
            ·
              refine ⟨12752737983837381220063685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8501825322558254146709123 12752737983837381220063685)
              ·
                refine ⟨2391138371969508978761941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12752737983837381220063685 2391138371969508978761941)
                ·
                  refine ⟨56042305593035366689733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2391138371969508978761941 56042305593035366689733)
                  ·
                    rfl

theorem cell22_491139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 7].length) (baseStart_491139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_491139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_491139 prefixEnd_491139 := by exact prefixLift 491139
  have htrace : WordTrace (prefixWord ++ tailWord_491139) baseStart_491139 baseEnd_491139 := by
    simpa [prefixWord, tailWord_491139, baseEnd_491139] using wordTrace_append hprefix tailTrace_491139
  have hstable : (prefixWord ++ tailWord_491139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491139).length < 2 ^ (prefixWord ++ tailWord_491139).sum := by decide
  have hdescent : baseEnd_491139 < baseStart_491139 := by decide
  rcases family_descends (prefixWord ++ tailWord_491139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491160 : List Nat := [2, 1, 2, 4, 1, 2, 2, 4, 1, 3]
def baseStart_491160 : Nat := 118140960795 + 491160 * 2 ^ 59
def prefixEnd_491160 : Nat := 4983230072969 + 3 ^ 40 * 491160 * 2
def baseEnd_491160 : Nat := 168134105508269045294135

theorem tailTrace_491160 : CollatzResearch.WordTrace tailWord_491160 prefixEnd_491160 168134105508269045294135 := by
  unfold tailWord_491160
  simp only [CollatzResearch.WordTrace]
  refine ⟨8957038450309339147403467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11942717933745785529871289 8957038450309339147403467)
  ·
    refine ⟨13435557675464008721105201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8957038450309339147403467 13435557675464008721105201)
    ·
      refine ⟨10076668256598006540828901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13435557675464008721105201 10076668256598006540828901)
      ·
        refine ⟨1889375298112126226405419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10076668256598006540828901 1889375298112126226405419)
        ·
          refine ⟨2834062947168189339608129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1889375298112126226405419 2834062947168189339608129)
          ·
            refine ⟨2125547210376142004706097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2834062947168189339608129 2125547210376142004706097)
            ·
              refine ⟨1594160407782106503529573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2125547210376142004706097 1594160407782106503529573)
              ·
                refine ⟨298905076459144969411795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1594160407782106503529573 298905076459144969411795)
                ·
                  refine ⟨448357614688717454117693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 298905076459144969411795 448357614688717454117693)
                  ·
                    refine ⟨168134105508269045294135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 448357614688717454117693 168134105508269045294135)
                    ·
                      rfl

theorem cell22_491160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 4, 1, 3].length) (baseStart_491160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_491160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_491160 prefixEnd_491160 := by exact prefixLift 491160
  have htrace : WordTrace (prefixWord ++ tailWord_491160) baseStart_491160 baseEnd_491160 := by
    simpa [prefixWord, tailWord_491160, baseEnd_491160] using wordTrace_append hprefix tailTrace_491160
  have hstable : (prefixWord ++ tailWord_491160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491160).length < 2 ^ (prefixWord ++ tailWord_491160).sum := by decide
  have hdescent : baseEnd_491160 < baseStart_491160 := by decide
  rcases family_descends (prefixWord ++ tailWord_491160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491186 : List Nat := [3, 2, 1, 1, 1, 2, 2, 3, 3, 4]
def baseStart_491186 : Nat := 118140960795 + 491186 * 2 ^ 59
def prefixEnd_491186 : Nat := 4983230072969 + 3 ^ 40 * 491186 * 2
def baseEnd_491186 : Nat := 168143005839613644144055

theorem tailTrace_491186 : CollatzResearch.WordTrace tailWord_491186 prefixEnd_491186 168143005839613644144055 := by
  unfold tailWord_491186
  simp only [CollatzResearch.WordTrace]
  refine ⟨4478756299631121183813353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11943350132349656490168941 4478756299631121183813353)
  ·
    refine ⟨3359067224723340887860015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4478756299631121183813353 3359067224723340887860015)
    ·
      refine ⟨5038600837085011331790023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3359067224723340887860015 5038600837085011331790023)
      ·
        refine ⟨7557901255627516997685035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5038600837085011331790023 7557901255627516997685035)
        ·
          refine ⟨11336851883441275496527553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7557901255627516997685035 11336851883441275496527553)
          ·
            refine ⟨8502638912580956622395665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11336851883441275496527553 8502638912580956622395665)
            ·
              refine ⟨6376979184435717466796749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8502638912580956622395665 6376979184435717466796749)
              ·
                refine ⟨2391367194163394050048781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6376979184435717466796749 2391367194163394050048781)
                ·
                  refine ⟨896762697811272768768293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2391367194163394050048781 896762697811272768768293)
                  ·
                    refine ⟨168143005839613644144055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 896762697811272768768293 168143005839613644144055)
                    ·
                      rfl

theorem cell22_491186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_491186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_491186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_491186 prefixEnd_491186 := by exact prefixLift 491186
  have htrace : WordTrace (prefixWord ++ tailWord_491186) baseStart_491186 baseEnd_491186 := by
    simpa [prefixWord, tailWord_491186, baseEnd_491186] using wordTrace_append hprefix tailTrace_491186
  have hstable : (prefixWord ++ tailWord_491186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491186).length < 2 ^ (prefixWord ++ tailWord_491186).sum := by decide
  have hdescent : baseEnd_491186 < baseStart_491186 := by decide
  rcases family_descends (prefixWord ++ tailWord_491186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491218 : List Nat := [3, 2, 2, 2, 2, 1, 3, 1, 6]
def baseStart_491218 : Nat := 118140960795 + 491218 * 2 ^ 59
def prefixEnd_491218 : Nat := 4983230072969 + 3 ^ 40 * 491218 * 2
def baseEnd_491218 : Nat := 56051320031192075781319

theorem tailTrace_491218 : CollatzResearch.WordTrace tailWord_491218 prefixEnd_491218 56051320031192075781319 := by
  unfold tailWord_491218
  simp only [CollatzResearch.WordTrace]
  refine ⟨4479048083602138550104577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11944128222939036133612205 4479048083602138550104577)
  ·
    refine ⟨3359286062701603912578433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4479048083602138550104577 3359286062701603912578433)
    ·
      refine ⟨2519464547026202934433825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3359286062701603912578433 2519464547026202934433825)
      ·
        refine ⟨1889598410269652200825369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2519464547026202934433825 1889598410269652200825369)
        ·
          refine ⟨1417198807702239150619027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1889598410269652200825369 1417198807702239150619027)
          ·
            refine ⟨2125798211553358725928541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1417198807702239150619027 2125798211553358725928541)
            ·
              refine ⟨797174329332509522223203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2125798211553358725928541 797174329332509522223203)
              ·
                refine ⟨1195761493998764283334805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 797174329332509522223203 1195761493998764283334805)
                ·
                  refine ⟨56051320031192075781319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1195761493998764283334805 56051320031192075781319)
                  ·
                    rfl

theorem cell22_491218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 1, 6].length) (baseStart_491218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_491218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_491218 prefixEnd_491218 := by exact prefixLift 491218
  have htrace : WordTrace (prefixWord ++ tailWord_491218) baseStart_491218 baseEnd_491218 := by
    simpa [prefixWord, tailWord_491218, baseEnd_491218] using wordTrace_append hprefix tailTrace_491218
  have hstable : (prefixWord ++ tailWord_491218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491218).length < 2 ^ (prefixWord ++ tailWord_491218).sum := by decide
  have hdescent : baseEnd_491218 < baseStart_491218 := by decide
  rcases family_descends (prefixWord ++ tailWord_491218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491231 : List Nat := [1, 1, 2, 3, 2, 2, 1, 2, 4, 4]
def baseStart_491231 : Nat := 118140960795 + 491231 * 2 ^ 59
def prefixEnd_491231 : Nat := 4983230072969 + 3 ^ 40 * 491231 * 2
def baseEnd_491231 : Nat := 168158410259248526768917

theorem tailTrace_491231 : CollatzResearch.WordTrace tailWord_491231 prefixEnd_491231 168158410259248526768917 := by
  unfold tailWord_491231
  simp only [CollatzResearch.WordTrace]
  refine ⟨17916666483361457420641547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11944444322240971613761031 17916666483361457420641547)
  ·
    refine ⟨26874999725042186130962321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17916666483361457420641547 26874999725042186130962321)
    ·
      refine ⟨20156249793781639598221741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26874999725042186130962321 20156249793781639598221741)
      ·
        refine ⟨7558593672668114849333153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20156249793781639598221741 7558593672668114849333153)
        ·
          refine ⟨5668945254501086136999865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7558593672668114849333153 5668945254501086136999865)
          ·
            refine ⟨4251708940875814602749899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5668945254501086136999865 4251708940875814602749899)
            ·
              refine ⟨6377563411313721904124849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4251708940875814602749899 6377563411313721904124849)
              ·
                refine ⟨4783172558485291428093637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6377563411313721904124849 4783172558485291428093637)
                ·
                  refine ⟨896844854715992142767557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4783172558485291428093637 896844854715992142767557)
                  ·
                    refine ⟨168158410259248526768917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 896844854715992142767557 168158410259248526768917)
                    ·
                      rfl

theorem cell22_491231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 4, 4].length) (baseStart_491231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_491231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_491231 prefixEnd_491231 := by exact prefixLift 491231
  have htrace : WordTrace (prefixWord ++ tailWord_491231) baseStart_491231 baseEnd_491231 := by
    simpa [prefixWord, tailWord_491231, baseEnd_491231] using wordTrace_append hprefix tailTrace_491231
  have hstable : (prefixWord ++ tailWord_491231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491231).length < 2 ^ (prefixWord ++ tailWord_491231).sum := by decide
  have hdescent : baseEnd_491231 < baseStart_491231 := by decide
  rcases family_descends (prefixWord ++ tailWord_491231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491246 : List Nat := [4, 1, 2, 1, 1, 2, 1, 10]
def baseStart_491246 : Nat := 118140960795 + 491246 * 2 ^ 59
def prefixEnd_491246 : Nat := 4983230072969 + 3 ^ 40 * 491246 * 2
def baseEnd_491246 : Nat := 18684838340643720849319

theorem tailTrace_491246 : CollatzResearch.WordTrace tailWord_491246 prefixEnd_491246 18684838340643720849319 := by
  unfold tailWord_491246
  simp only [CollatzResearch.WordTrace]
  refine ⟨2239651697288389372804699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11944809052204743321625061 2239651697288389372804699)
  ·
    refine ⟨3359477545932584059207049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2239651697288389372804699 3359477545932584059207049)
    ·
      refine ⟨2519608159449438044405287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3359477545932584059207049 2519608159449438044405287)
      ·
        refine ⟨3779412239174157066607931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2519608159449438044405287 3779412239174157066607931)
        ·
          refine ⟨5669118358761235599911897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3779412239174157066607931 5669118358761235599911897)
          ·
            refine ⟨4251838769070926699933923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5669118358761235599911897 4251838769070926699933923)
            ·
              refine ⟨6377758153606390049900885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4251838769070926699933923 6377758153606390049900885)
              ·
                refine ⟨18684838340643720849319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 6377758153606390049900885 18684838340643720849319)
                ·
                  rfl

theorem cell22_491246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 10].length) (baseStart_491246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_491246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_491246 prefixEnd_491246 := by exact prefixLift 491246
  have htrace : WordTrace (prefixWord ++ tailWord_491246) baseStart_491246 baseEnd_491246 := by
    simpa [prefixWord, tailWord_491246, baseEnd_491246] using wordTrace_append hprefix tailTrace_491246
  have hstable : (prefixWord ++ tailWord_491246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491246).length < 2 ^ (prefixWord ++ tailWord_491246).sum := by decide
  have hdescent : baseEnd_491246 < baseStart_491246 := by decide
  rcases family_descends (prefixWord ++ tailWord_491246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491276 : List Nat := [2, 2, 1, 2, 2, 1, 3, 1, 2, 6]
def baseStart_491276 : Nat := 118140960795 + 491276 * 2 ^ 59
def prefixEnd_491276 : Nat := 4983230072969 + 3 ^ 40 * 491276 * 2
def baseEnd_491276 : Nat := 168173814678883409393779

theorem tailTrace_491276 : CollatzResearch.WordTrace tailWord_491276 prefixEnd_491276 168173814678883409393779 := by
  unfold tailWord_491276
  simp only [CollatzResearch.WordTrace]
  refine ⟨8959153884099215053014841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11945538512132286737353121 8959153884099215053014841)
  ·
    refine ⟨6719365413074411289761131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8959153884099215053014841 6719365413074411289761131)
    ·
      refine ⟨10079048119611616934641697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6719365413074411289761131 10079048119611616934641697)
      ·
        refine ⟨7559286089708712700981273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10079048119611616934641697 7559286089708712700981273)
        ·
          refine ⟨5669464567281534525735955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7559286089708712700981273 5669464567281534525735955)
          ·
            refine ⟨8504196850922301788603933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5669464567281534525735955 8504196850922301788603933)
            ·
              refine ⟨3189073819095863170726475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8504196850922301788603933 3189073819095863170726475)
              ·
                refine ⟨4783610728643794756089713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3189073819095863170726475 4783610728643794756089713)
                ·
                  refine ⟨3587708046482846067067285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4783610728643794756089713 3587708046482846067067285)
                  ·
                    refine ⟨168173814678883409393779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3587708046482846067067285 168173814678883409393779)
                    ·
                      rfl

theorem cell22_491276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 2, 6].length) (baseStart_491276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_491276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_491276 prefixEnd_491276 := by exact prefixLift 491276
  have htrace : WordTrace (prefixWord ++ tailWord_491276) baseStart_491276 baseEnd_491276 := by
    simpa [prefixWord, tailWord_491276, baseEnd_491276] using wordTrace_append hprefix tailTrace_491276
  have hstable : (prefixWord ++ tailWord_491276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491276).length < 2 ^ (prefixWord ++ tailWord_491276).sum := by decide
  have hdescent : baseEnd_491276 < baseStart_491276 := by decide
  rcases family_descends (prefixWord ++ tailWord_491276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491284 : List Nat := [2, 4, 4, 1, 1, 1, 2, 1, 1, 5]
def baseStart_491284 : Nat := 118140960795 + 491284 * 2 ^ 59
def prefixEnd_491284 : Nat := 4983230072969 + 3 ^ 40 * 491284 * 2
def baseEnd_491284 : Nat := 168176553242374055193755

theorem tailTrace_491284 : CollatzResearch.WordTrace tailWord_491284 prefixEnd_491284 168176553242374055193755 := by
  unfold tailWord_491284
  simp only [CollatzResearch.WordTrace]
  refine ⟨8959299776084723736160453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11945733034779631648213937 8959299776084723736160453)
  ·
    refine ⟨1679868708015885700530085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8959299776084723736160453 1679868708015885700530085)
    ·
      refine ⟨314975382752978568849391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1679868708015885700530085 314975382752978568849391)
      ·
        refine ⟨472463074129467853274087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314975382752978568849391 472463074129467853274087)
        ·
          refine ⟨708694611194201779911131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 472463074129467853274087 708694611194201779911131)
          ·
            refine ⟨1063041916791302669866697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 708694611194201779911131 1063041916791302669866697)
            ·
              refine ⟨797281437593477002400023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1063041916791302669866697 797281437593477002400023)
              ·
                refine ⟨1195922156390215503600035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 797281437593477002400023 1195922156390215503600035)
                ·
                  refine ⟨1793883234585323255400053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1195922156390215503600035 1793883234585323255400053)
                  ·
                    refine ⟨168176553242374055193755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1793883234585323255400053 168176553242374055193755)
                    ·
                      rfl

theorem cell22_491284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_491284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_491284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_491284 prefixEnd_491284 := by exact prefixLift 491284
  have htrace : WordTrace (prefixWord ++ tailWord_491284) baseStart_491284 baseEnd_491284 := by
    simpa [prefixWord, tailWord_491284, baseEnd_491284] using wordTrace_append hprefix tailTrace_491284
  have hstable : (prefixWord ++ tailWord_491284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491284).length < 2 ^ (prefixWord ++ tailWord_491284).sum := by decide
  have hdescent : baseEnd_491284 < baseStart_491284 := by decide
  rcases family_descends (prefixWord ++ tailWord_491284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491325 : List Nat := [1, 4, 1, 4, 1, 1, 3, 2, 5]
def baseStart_491325 : Nat := 118140960795 + 491325 * 2 ^ 59
def prefixEnd_491325 : Nat := 4983230072969 + 3 ^ 40 * 491325 * 2
def baseEnd_491325 : Nat := 56063529460087871639543

theorem tailTrace_491325 : CollatzResearch.WordTrace tailWord_491325 prefixEnd_491325 56063529460087871639543 := by
  unfold tailWord_491325
  simp only [CollatzResearch.WordTrace]
  refine ⟨17920094945020911474563429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11946729963347274316375619 17920094945020911474563429)
  ·
    refine ⟨3360017802191420901480643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17920094945020911474563429 3360017802191420901480643)
    ·
      refine ⟨5040026703287131352220965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3360017802191420901480643 5040026703287131352220965)
      ·
        refine ⟨945005006866337128541431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5040026703287131352220965 945005006866337128541431)
        ·
          refine ⟨1417507510299505692812147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 945005006866337128541431 1417507510299505692812147)
          ·
            refine ⟨2126261265449258539218221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1417507510299505692812147 2126261265449258539218221)
            ·
              refine ⟨797347974543471952206833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2126261265449258539218221 797347974543471952206833)
              ·
                refine ⟨598010980907603964155125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 797347974543471952206833 598010980907603964155125)
                ·
                  refine ⟨56063529460087871639543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 598010980907603964155125 56063529460087871639543)
                  ·
                    rfl

theorem cell22_491325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 2, 5].length) (baseStart_491325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_491325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_491325 prefixEnd_491325 := by exact prefixLift 491325
  have htrace : WordTrace (prefixWord ++ tailWord_491325) baseStart_491325 baseEnd_491325 := by
    simpa [prefixWord, tailWord_491325, baseEnd_491325] using wordTrace_append hprefix tailTrace_491325
  have hstable : (prefixWord ++ tailWord_491325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491325).length < 2 ^ (prefixWord ++ tailWord_491325).sum := by decide
  have hdescent : baseEnd_491325 < baseStart_491325 := by decide
  rcases family_descends (prefixWord ++ tailWord_491325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491368 : List Nat := [2, 1, 4, 2, 1, 1, 2, 1, 3, 5]
def baseStart_491368 : Nat := 118140960795 + 491368 * 2 ^ 59
def prefixEnd_491368 : Nat := 4983230072969 + 3 ^ 40 * 491368 * 2
def baseEnd_491368 : Nat := 168205308159025836093497

theorem tailTrace_491368 : CollatzResearch.WordTrace tailWord_491368 prefixEnd_491368 168205308159025836093497 := by
  unfold tailWord_491368
  simp only [CollatzResearch.WordTrace]
  refine ⟨8960831641932564909189379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11947775522576753212252505 8960831641932564909189379)
  ·
    refine ⟨13441247462898847363784069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8960831641932564909189379 13441247462898847363784069)
    ·
      refine ⟨2520233899293533880709513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13441247462898847363784069 2520233899293533880709513)
      ·
        refine ⟨1890175424470150410532135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2520233899293533880709513 1890175424470150410532135)
        ·
          refine ⟨2835263136705225615798203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1890175424470150410532135 2835263136705225615798203)
          ·
            refine ⟨4252894705057838423697305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2835263136705225615798203 4252894705057838423697305)
            ·
              refine ⟨3189671028793378817772979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4252894705057838423697305 3189671028793378817772979)
              ·
                refine ⟨4784506543190068226659469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3189671028793378817772979 4784506543190068226659469)
                ·
                  refine ⟨1794189953696275584997301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4784506543190068226659469 1794189953696275584997301)
                  ·
                    refine ⟨168205308159025836093497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1794189953696275584997301 168205308159025836093497)
                    ·
                      rfl

theorem cell22_491368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_491368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_491368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_491368 prefixEnd_491368 := by exact prefixLift 491368
  have htrace : WordTrace (prefixWord ++ tailWord_491368) baseStart_491368 baseEnd_491368 := by
    simpa [prefixWord, tailWord_491368, baseEnd_491368] using wordTrace_append hprefix tailTrace_491368
  have hstable : (prefixWord ++ tailWord_491368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491368).length < 2 ^ (prefixWord ++ tailWord_491368).sum := by decide
  have hdescent : baseEnd_491368 < baseStart_491368 := by decide
  rcases family_descends (prefixWord ++ tailWord_491368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491385 : List Nat := [1, 2, 1, 3, 2, 2, 2, 4, 2, 3]
def baseStart_491385 : Nat := 118140960795 + 491385 * 2 ^ 59
def prefixEnd_491385 : Nat := 4983230072969 + 3 ^ 40 * 491385 * 2
def baseEnd_491385 : Nat := 168211127606443458418445

theorem tailTrace_491385 : CollatzResearch.WordTrace tailWord_491385 prefixEnd_491385 168211127606443458418445 := by
  unfold tailWord_491385
  simp only [CollatzResearch.WordTrace]
  refine ⟨17922283324803541721747609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11948188883202361147831739 17922283324803541721747609)
  ·
    refine ⟨13441712493602656291310707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17922283324803541721747609 13441712493602656291310707)
    ·
      refine ⟨20162568740403984436966061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13441712493602656291310707 20162568740403984436966061)
      ·
        refine ⟨7560963277651494163862273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20162568740403984436966061 7560963277651494163862273)
        ·
          refine ⟨5670722458238620622896705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7560963277651494163862273 5670722458238620622896705)
          ·
            refine ⟨4253041843678965467172529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5670722458238620622896705 4253041843678965467172529)
            ·
              refine ⟨3189781382759224100379397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4253041843678965467172529 3189781382759224100379397)
              ·
                refine ⟨598084009267354518821137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3189781382759224100379397 598084009267354518821137)
                ·
                  refine ⟨448563006950515889115853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 598084009267354518821137 448563006950515889115853)
                  ·
                    refine ⟨168211127606443458418445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 448563006950515889115853 168211127606443458418445)
                    ·
                      rfl

theorem cell22_491385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 4, 2, 3].length) (baseStart_491385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_491385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_491385 prefixEnd_491385 := by exact prefixLift 491385
  have htrace : WordTrace (prefixWord ++ tailWord_491385) baseStart_491385 baseEnd_491385 := by
    simpa [prefixWord, tailWord_491385, baseEnd_491385] using wordTrace_append hprefix tailTrace_491385
  have hstable : (prefixWord ++ tailWord_491385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491385).length < 2 ^ (prefixWord ++ tailWord_491385).sum := by decide
  have hdescent : baseEnd_491385 < baseStart_491385 := by decide
  rcases family_descends (prefixWord ++ tailWord_491385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491406 : List Nat := [4, 1, 1, 5, 2, 1, 1, 2, 1, 4]
def baseStart_491406 : Nat := 118140960795 + 491406 * 2 ^ 59
def prefixEnd_491406 : Nat := 4983230072969 + 3 ^ 40 * 491406 * 2
def baseEnd_491406 : Nat := 168218316335606403643381

theorem tailTrace_491406 : CollatzResearch.WordTrace tailWord_491406 prefixEnd_491406 168218316335606403643381 := by
  unfold tailWord_491406
  simp only [CollatzResearch.WordTrace]
  refine ⟨2240381157215932788532759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11948699505151641538841381 2240381157215932788532759)
  ·
    refine ⟨3360571735823899182799139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2240381157215932788532759 3360571735823899182799139)
    ·
      refine ⟨5040857603735848774198709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3360571735823899182799139 5040857603735848774198709)
      ·
        refine ⟨472580400350235822581129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5040857603735848774198709 472580400350235822581129)
        ·
          refine ⟨354435300262676866935847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 472580400350235822581129 354435300262676866935847)
          ·
            refine ⟨531652950394015300403771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354435300262676866935847 531652950394015300403771)
            ·
              refine ⟨797479425591022950605657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 531652950394015300403771 797479425591022950605657)
              ·
                refine ⟨598109569193267212954243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 797479425591022950605657 598109569193267212954243)
                ·
                  refine ⟨897164353789900819431365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 598109569193267212954243 897164353789900819431365)
                  ·
                    refine ⟨168218316335606403643381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 897164353789900819431365 168218316335606403643381)
                    ·
                      rfl

theorem cell22_491406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 2, 1, 4].length) (baseStart_491406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_491406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_491406 prefixEnd_491406 := by exact prefixLift 491406
  have htrace : WordTrace (prefixWord ++ tailWord_491406) baseStart_491406 baseEnd_491406 := by
    simpa [prefixWord, tailWord_491406, baseEnd_491406] using wordTrace_append hprefix tailTrace_491406
  have hstable : (prefixWord ++ tailWord_491406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491406).length < 2 ^ (prefixWord ++ tailWord_491406).sum := by decide
  have hdescent : baseEnd_491406 < baseStart_491406 := by decide
  rcases family_descends (prefixWord ++ tailWord_491406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491432 : List Nat := [2, 1, 6, 2, 2, 9]
def baseStart_491432 : Nat := 118140960795 + 491432 * 2 ^ 59
def prefixEnd_491432 : Nat := 4983230072969 + 3 ^ 40 * 491432 * 2
def baseEnd_491432 : Nat := 2076879218110506203621

theorem tailTrace_491432 : CollatzResearch.WordTrace tailWord_491432 prefixEnd_491432 2076879218110506203621 := by
  unfold tailWord_491432
  simp only [CollatzResearch.WordTrace]
  refine ⟨8961998777816634374354275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11949331703755512499139033 8961998777816634374354275)
  ·
    refine ⟨13442998166724951561531413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8961998777816634374354275 13442998166724951561531413)
    ·
      refine ⟨630140539065232104446785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 13442998166724951561531413 630140539065232104446785)
      ·
        refine ⟨472605404298924078335089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 630140539065232104446785 472605404298924078335089)
        ·
          refine ⟨354454053224193058751317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 472605404298924078335089 354454053224193058751317)
          ·
            refine ⟨2076879218110506203621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 354454053224193058751317 2076879218110506203621)
            ·
              rfl

theorem cell22_491432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 9].length) (baseStart_491432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_491432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_491432 prefixEnd_491432 := by exact prefixLift 491432
  have htrace : WordTrace (prefixWord ++ tailWord_491432) baseStart_491432 baseEnd_491432 := by
    simpa [prefixWord, tailWord_491432, baseEnd_491432] using wordTrace_append hprefix tailTrace_491432
  have hstable : (prefixWord ++ tailWord_491432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491432).length < 2 ^ (prefixWord ++ tailWord_491432).sum := by decide
  have hdescent : baseEnd_491432 < baseStart_491432 := by decide
  rcases family_descends (prefixWord ++ tailWord_491432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491556 : List Nat := [2, 3, 1, 4, 2, 1, 3, 2, 4]
def baseStart_491556 : Nat := 118140960795 + 491556 * 2 ^ 59
def prefixEnd_491556 : Nat := 4983230072969 + 3 ^ 40 * 491556 * 2
def baseEnd_491556 : Nat := 56089888133685337464307

theorem tailTrace_491556 : CollatzResearch.WordTrace tailWord_491556 prefixEnd_491556 56089888133685337464307 := by
  unfold tailWord_491556
  simp only [CollatzResearch.WordTrace]
  refine ⟨8964260103592018963111261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11952346804789358617481681 8964260103592018963111261)
  ·
    refine ⟨3361597538847007111166723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8964260103592018963111261 3361597538847007111166723)
    ·
      refine ⟨5042396308270510666750085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3361597538847007111166723 5042396308270510666750085)
      ·
        refine ⟨945449307800720750015641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5042396308270510666750085 945449307800720750015641)
        ·
          refine ⟨709086980850540562511731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 945449307800720750015641 709086980850540562511731)
          ·
            refine ⟨1063630471275810843767597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 709086980850540562511731 1063630471275810843767597)
            ·
              refine ⟨398861426728429066412849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1063630471275810843767597 398861426728429066412849)
              ·
                refine ⟨299146070046321799809637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 398861426728429066412849 299146070046321799809637)
                ·
                  refine ⟨56089888133685337464307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 299146070046321799809637 56089888133685337464307)
                  ·
                    rfl

theorem cell22_491556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 3, 2, 4].length) (baseStart_491556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_491556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_491556 prefixEnd_491556 := by exact prefixLift 491556
  have htrace : WordTrace (prefixWord ++ tailWord_491556) baseStart_491556 baseEnd_491556 := by
    simpa [prefixWord, tailWord_491556, baseEnd_491556] using wordTrace_append hprefix tailTrace_491556
  have hstable : (prefixWord ++ tailWord_491556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491556).length < 2 ^ (prefixWord ++ tailWord_491556).sum := by decide
  have hdescent : baseEnd_491556 < baseStart_491556 := by decide
  rcases family_descends (prefixWord ++ tailWord_491556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491610 : List Nat := [3, 1, 1, 2, 1, 1, 4, 2, 2, 5]
def baseStart_491610 : Nat := 118140960795 + 491610 * 2 ^ 59
def prefixEnd_491610 : Nat := 4983230072969 + 3 ^ 40 * 491610 * 2
def baseEnd_491610 : Nat := 168288149704617871542755

theorem tailTrace_491610 : CollatzResearch.WordTrace tailWord_491610 prefixEnd_491610 168288149704617871542755 := by
  unfold tailWord_491610
  simp only [CollatzResearch.WordTrace]
  refine ⟨4482622437247101287172071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11953659832658936765792189 4482622437247101287172071)
  ·
    refine ⟨6723933655870651930758107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4482622437247101287172071 6723933655870651930758107)
    ·
      refine ⟨10085900483805977896137161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6723933655870651930758107 10085900483805977896137161)
      ·
        refine ⟨7564425362854483422102871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10085900483805977896137161 7564425362854483422102871)
        ·
          refine ⟨11346638044281725133154307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7564425362854483422102871 11346638044281725133154307)
          ·
            refine ⟨17019957066422587699731461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11346638044281725133154307 17019957066422587699731461)
            ·
              refine ⟨3191241949954235193699649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17019957066422587699731461 3191241949954235193699649)
              ·
                refine ⟨2393431462465676395274737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3191241949954235193699649 2393431462465676395274737)
                ·
                  refine ⟨1795073596849257296456053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2393431462465676395274737 1795073596849257296456053)
                  ·
                    refine ⟨168288149704617871542755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1795073596849257296456053 168288149704617871542755)
                    ·
                      rfl

theorem cell22_491610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 2, 5].length) (baseStart_491610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_491610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_491610 prefixEnd_491610 := by exact prefixLift 491610
  have htrace : WordTrace (prefixWord ++ tailWord_491610) baseStart_491610 baseEnd_491610 := by
    simpa [prefixWord, tailWord_491610, baseEnd_491610] using wordTrace_append hprefix tailTrace_491610
  have hstable : (prefixWord ++ tailWord_491610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491610).length < 2 ^ (prefixWord ++ tailWord_491610).sum := by decide
  have hdescent : baseEnd_491610 < baseStart_491610 := by decide
  rcases family_descends (prefixWord ++ tailWord_491610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491612 : List Nat := [2, 2, 4, 1, 1, 2, 1, 4, 5]
def baseStart_491612 : Nat := 118140960795 + 491612 * 2 ^ 59
def prefixEnd_491612 : Nat := 4983230072969 + 3 ^ 40 * 491612 * 2
def baseEnd_491612 : Nat := 56096278115163510997583

theorem tailTrace_491612 : CollatzResearch.WordTrace tailWord_491612 prefixEnd_491612 56096278115163510997583 := by
  unfold tailWord_491612
  simp only [CollatzResearch.WordTrace]
  refine ⟨8965281347490579745130545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11953708463320772993507393 8965281347490579745130545)
  ·
    refine ⟨6723961010617934808847909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8965281347490579745130545 6723961010617934808847909)
    ·
      refine ⟨1260742689490862776658983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6723961010617934808847909 1260742689490862776658983)
      ·
        refine ⟨1891114034236294164988475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1260742689490862776658983 1891114034236294164988475)
        ·
          refine ⟨2836671051354441247482713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1891114034236294164988475 2836671051354441247482713)
          ·
            refine ⟨2127503288515830935612035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2836671051354441247482713 2127503288515830935612035)
            ·
              refine ⟨3191254932773746403418053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2127503288515830935612035 3191254932773746403418053)
              ·
                refine ⟨598360299895077450640885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3191254932773746403418053 598360299895077450640885)
                ·
                  refine ⟨56096278115163510997583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 598360299895077450640885 56096278115163510997583)
                  ·
                    rfl

theorem cell22_491612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 4, 5].length) (baseStart_491612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_491612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_491612 prefixEnd_491612 := by exact prefixLift 491612
  have htrace : WordTrace (prefixWord ++ tailWord_491612) baseStart_491612 baseEnd_491612 := by
    simpa [prefixWord, tailWord_491612, baseEnd_491612] using wordTrace_append hprefix tailTrace_491612
  have hstable : (prefixWord ++ tailWord_491612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491612).length < 2 ^ (prefixWord ++ tailWord_491612).sum := by decide
  have hdescent : baseEnd_491612 < baseStart_491612 := by decide
  rcases family_descends (prefixWord ++ tailWord_491612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491616 : List Nat := [2, 1, 1, 3, 2, 3, 4, 2, 1, 3]
def baseStart_491616 : Nat := 118140960795 + 491616 * 2 ^ 59
def prefixEnd_491616 : Nat := 4983230072969 + 3 ^ 40 * 491616 * 2
def baseEnd_491616 : Nat := 168290203627235855892737

theorem tailTrace_491616 : CollatzResearch.WordTrace tailWord_491616 prefixEnd_491616 168290203627235855892737 := by
  unfold tailWord_491616
  simp only [CollatzResearch.WordTrace]
  refine ⟨8965354293483334086703351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11953805724644445448937801 8965354293483334086703351)
  ·
    refine ⟨13448031440225001130055027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8965354293483334086703351 13448031440225001130055027)
    ·
      refine ⟨20172047160337501695082541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13448031440225001130055027 20172047160337501695082541)
      ·
        refine ⟨7564517685126563135655953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20172047160337501695082541 7564517685126563135655953)
        ·
          refine ⟨5673388263844922351741965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7564517685126563135655953 5673388263844922351741965)
          ·
            refine ⟨2127520598941845881903237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5673388263844922351741965 2127520598941845881903237)
            ·
              refine ⟨398910112301596102856857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2127520598941845881903237 398910112301596102856857)
              ·
                refine ⟨299182584226197077142643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 398910112301596102856857 299182584226197077142643)
                ·
                  refine ⟨448773876339295615713965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 299182584226197077142643 448773876339295615713965)
                  ·
                    refine ⟨168290203627235855892737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 448773876339295615713965 168290203627235855892737)
                    ·
                      rfl

theorem cell22_491616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 4, 2, 1, 3].length) (baseStart_491616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_491616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_491616 prefixEnd_491616 := by exact prefixLift 491616
  have htrace : WordTrace (prefixWord ++ tailWord_491616) baseStart_491616 baseEnd_491616 := by
    simpa [prefixWord, tailWord_491616, baseEnd_491616] using wordTrace_append hprefix tailTrace_491616
  have hstable : (prefixWord ++ tailWord_491616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491616).length < 2 ^ (prefixWord ++ tailWord_491616).sum := by decide
  have hdescent : baseEnd_491616 < baseStart_491616 := by decide
  rcases family_descends (prefixWord ++ tailWord_491616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491625 : List Nat := [1, 2, 1, 1, 1, 5, 1, 1, 5, 4]
def baseStart_491625 : Nat := 118140960795 + 491625 * 2 ^ 59
def prefixEnd_491625 : Nat := 4983230072969 + 3 ^ 40 * 491625 * 2
def baseEnd_491625 : Nat := 168293284511162832417709

theorem tailTrace_491625 : CollatzResearch.WordTrace tailWord_491625 prefixEnd_491625 168293284511162832417709 := by
  unfold tailWord_491625
  simp only [CollatzResearch.WordTrace]
  refine ⟨17931036843934062710484329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11954024562622708473656219 17931036843934062710484329)
  ·
    refine ⟨13448277632950547032863247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17931036843934062710484329 13448277632950547032863247)
    ·
      refine ⟨20172416449425820549294871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13448277632950547032863247 20172416449425820549294871)
      ·
        refine ⟨30258624674138730823942307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20172416449425820549294871 30258624674138730823942307)
        ·
          refine ⟨45387937011208096235913461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30258624674138730823942307 45387937011208096235913461)
          ·
            refine ⟨4255119094800759022116887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45387937011208096235913461 4255119094800759022116887)
            ·
              refine ⟨6382678642201138533175331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4255119094800759022116887 6382678642201138533175331)
              ·
                refine ⟨9574017963301707799762997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6382678642201138533175331 9574017963301707799762997)
                ·
                  refine ⟨897564184059535106227781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9574017963301707799762997 897564184059535106227781)
                  ·
                    refine ⟨168293284511162832417709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 897564184059535106227781 168293284511162832417709)
                    ·
                      rfl

theorem cell22_491625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 5, 4].length) (baseStart_491625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_491625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_491625 prefixEnd_491625 := by exact prefixLift 491625
  have htrace : WordTrace (prefixWord ++ tailWord_491625) baseStart_491625 baseEnd_491625 := by
    simpa [prefixWord, tailWord_491625, baseEnd_491625] using wordTrace_append hprefix tailTrace_491625
  have hstable : (prefixWord ++ tailWord_491625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491625).length < 2 ^ (prefixWord ++ tailWord_491625).sum := by decide
  have hdescent : baseEnd_491625 < baseStart_491625 := by decide
  rcases family_descends (prefixWord ++ tailWord_491625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491674 : List Nat := [3, 1, 1, 5, 2, 1, 2, 1, 6]
def baseStart_491674 : Nat := 118140960795 + 491674 * 2 ^ 59
def prefixEnd_491674 : Nat := 4983230072969 + 3 ^ 40 * 491674 * 2
def baseEnd_491674 : Nat := 56103352737514345980853

theorem tailTrace_491674 : CollatzResearch.WordTrace tailWord_491674 prefixEnd_491674 56103352737514345980853 := by
  unfold tailWord_491674
  simp only [CollatzResearch.WordTrace]
  refine ⟨4483206005189136019754519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11955216013837696052678717 4483206005189136019754519)
  ·
    refine ⟨6724809007783704029631779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4483206005189136019754519 6724809007783704029631779)
    ·
      refine ⟨10087213511675556044447669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6724809007783704029631779 10087213511675556044447669)
      ·
        refine ⟨945676266719583379166969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10087213511675556044447669 945676266719583379166969)
        ·
          refine ⟨709257200039687534375227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 945676266719583379166969 709257200039687534375227)
          ·
            refine ⟨1063885800059531301562841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 709257200039687534375227 1063885800059531301562841)
            ·
              refine ⟨797914350044648476172131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1063885800059531301562841 797914350044648476172131)
              ·
                refine ⟨1196871525066972714258197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 797914350044648476172131 1196871525066972714258197)
                ·
                  refine ⟨56103352737514345980853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1196871525066972714258197 56103352737514345980853)
                  ·
                    rfl

theorem cell22_491674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 1, 6].length) (baseStart_491674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_491674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_491674 prefixEnd_491674 := by exact prefixLift 491674
  have htrace : WordTrace (prefixWord ++ tailWord_491674) baseStart_491674 baseEnd_491674 := by
    simpa [prefixWord, tailWord_491674, baseEnd_491674] using wordTrace_append hprefix tailTrace_491674
  have hstable : (prefixWord ++ tailWord_491674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491674).length < 2 ^ (prefixWord ++ tailWord_491674).sum := by decide
  have hdescent : baseEnd_491674 < baseStart_491674 := by decide
  rcases family_descends (prefixWord ++ tailWord_491674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491685 : List Nat := [1, 3, 1, 2, 1, 3, 2, 9]
def baseStart_491685 : Nat := 118140960795 + 491685 * 2 ^ 59
def prefixEnd_491685 : Nat := 4983230072969 + 3 ^ 40 * 491685 * 2
def baseEnd_491685 : Nat := 18701535970815852879725

theorem tailTrace_491685 : CollatzResearch.WordTrace tailWord_491685 prefixEnd_491685 18701535970815852879725 := by
  unfold tailWord_491685
  simp only [CollatzResearch.WordTrace]
  refine ⟨17933225223716692957668509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11955483482477795305112339 17933225223716692957668509)
  ·
    refine ⟨6724959458893759859125691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17933225223716692957668509 6724959458893759859125691)
    ·
      refine ⟨10087439188340639788688537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6724959458893759859125691 10087439188340639788688537)
      ·
        refine ⟨7565579391255479841516403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10087439188340639788688537 7565579391255479841516403)
        ·
          refine ⟨11348369086883219762274605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7565579391255479841516403 11348369086883219762274605)
          ·
            refine ⟨4255638407581207410852977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11348369086883219762274605 4255638407581207410852977)
            ·
              refine ⟨3191728805685905558139733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4255638407581207410852977 3191728805685905558139733)
              ·
                refine ⟨18701535970815852879725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3191728805685905558139733 18701535970815852879725)
                ·
                  rfl

theorem cell22_491685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 9].length) (baseStart_491685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_491685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_491685 prefixEnd_491685 := by exact prefixLift 491685
  have htrace : WordTrace (prefixWord ++ tailWord_491685) baseStart_491685 baseEnd_491685 := by
    simpa [prefixWord, tailWord_491685, baseEnd_491685] using wordTrace_append hprefix tailTrace_491685
  have hstable : (prefixWord ++ tailWord_491685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491685).length < 2 ^ (prefixWord ++ tailWord_491685).sum := by decide
  have hdescent : baseEnd_491685 < baseStart_491685 := by decide
  rcases family_descends (prefixWord ++ tailWord_491685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491708 : List Nat := [2, 2, 2, 3, 4, 1, 1, 3, 4]
def baseStart_491708 : Nat := 118140960795 + 491708 * 2 ^ 59
def prefixEnd_491708 : Nat := 4983230072969 + 3 ^ 40 * 491708 * 2
def baseEnd_491708 : Nat := 56107232369126094197485

theorem tailTrace_491708 : CollatzResearch.WordTrace tailWord_491708 prefixEnd_491708 56107232369126094197485 := by
  unfold tailWord_491708
  simp only [CollatzResearch.WordTrace]
  refine ⟨8967032051316683942877889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11956042735088911923837185 8967032051316683942877889)
  ·
    refine ⟨6725274038487512957158417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8967032051316683942877889 6725274038487512957158417)
    ·
      refine ⟨5043955528865634717868813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6725274038487512957158417 5043955528865634717868813)
      ·
        refine ⟨1891483323324613019200805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5043955528865634717868813 1891483323324613019200805)
        ·
          refine ⟨354653123123364941100151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1891483323324613019200805 354653123123364941100151)
          ·
            refine ⟨531979684685047411650227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354653123123364941100151 531979684685047411650227)
            ·
              refine ⟨797969527027571117475341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 531979684685047411650227 797969527027571117475341)
              ·
                refine ⟨299238572635339169053253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 797969527027571117475341 299238572635339169053253)
                ·
                  refine ⟨56107232369126094197485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 299238572635339169053253 56107232369126094197485)
                  ·
                    rfl

theorem cell22_491708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 3, 4].length) (baseStart_491708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_491708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_491708 prefixEnd_491708 := by exact prefixLift 491708
  have htrace : WordTrace (prefixWord ++ tailWord_491708) baseStart_491708 baseEnd_491708 := by
    simpa [prefixWord, tailWord_491708, baseEnd_491708] using wordTrace_append hprefix tailTrace_491708
  have hstable : (prefixWord ++ tailWord_491708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491708).length < 2 ^ (prefixWord ++ tailWord_491708).sum := by decide
  have hdescent : baseEnd_491708 < baseStart_491708 := by decide
  rcases family_descends (prefixWord ++ tailWord_491708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491717 : List Nat := [1, 3, 1, 1, 1, 1, 4, 2, 5, 3]
def baseStart_491717 : Nat := 118140960795 + 491717 * 2 ^ 59
def prefixEnd_491717 : Nat := 4983230072969 + 3 ^ 40 * 491717 * 2
def baseEnd_491717 : Nat := 168324777991305259117427

theorem tailTrace_491717 : CollatzResearch.WordTrace tailWord_491717 prefixEnd_491717 168324777991305259117427 := by
  unfold tailWord_491717
  simp only [CollatzResearch.WordTrace]
  refine ⟨17934392359600762422833405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11956261573067174948555603 17934392359600762422833405)
  ·
    refine ⟨6725397134850285908562527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17934392359600762422833405 6725397134850285908562527)
    ·
      refine ⟨10088095702275428862843791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6725397134850285908562527 10088095702275428862843791)
      ·
        refine ⟨15132143553413143294265687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10088095702275428862843791 15132143553413143294265687)
        ·
          refine ⟨22698215330119714941398531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15132143553413143294265687 22698215330119714941398531)
          ·
            refine ⟨34047322995179572412097797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22698215330119714941398531 34047322995179572412097797)
            ·
              refine ⟨6383873061596169827268337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34047322995179572412097797 6383873061596169827268337)
              ·
                refine ⟨4787904796197127370451253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6383873061596169827268337 4787904796197127370451253)
                ·
                  refine ⟨448866074643480690979805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4787904796197127370451253 448866074643480690979805)
                  ·
                    refine ⟨168324777991305259117427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 448866074643480690979805 168324777991305259117427)
                    ·
                      rfl

theorem cell22_491717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 5, 3].length) (baseStart_491717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_491717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_491717 prefixEnd_491717 := by exact prefixLift 491717
  have htrace : WordTrace (prefixWord ++ tailWord_491717) baseStart_491717 baseEnd_491717 := by
    simpa [prefixWord, tailWord_491717, baseEnd_491717] using wordTrace_append hprefix tailTrace_491717
  have hstable : (prefixWord ++ tailWord_491717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491717).length < 2 ^ (prefixWord ++ tailWord_491717).sum := by decide
  have hdescent : baseEnd_491717 < baseStart_491717 := by decide
  rcases family_descends (prefixWord ++ tailWord_491717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491828 : List Nat := [2, 5, 1, 1, 1, 2, 4, 1, 1, 4]
def baseStart_491828 : Nat := 118140960795 + 491828 * 2 ^ 59
def prefixEnd_491828 : Nat := 4983230072969 + 3 ^ 40 * 491828 * 2
def baseEnd_491828 : Nat := 168362775559737969592087

theorem tailTrace_491828 : CollatzResearch.WordTrace tailWord_491828 prefixEnd_491828 168362775559737969592087 := by
  unfold tailWord_491828
  simp only [CollatzResearch.WordTrace]
  refine ⟨8969220431099314190062069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11958960574799085586749425 8969220431099314190062069)
  ·
    refine ⟨840864415415560705318319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8969220431099314190062069 840864415415560705318319)
    ·
      refine ⟨1261296623123341057977479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 840864415415560705318319 1261296623123341057977479)
      ·
        refine ⟨1891944934685011586966219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1261296623123341057977479 1891944934685011586966219)
        ·
          refine ⟨2837917402027517380449329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1891944934685011586966219 2837917402027517380449329)
          ·
            refine ⟨2128438051520638035336997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2837917402027517380449329 2128438051520638035336997)
            ·
              refine ⟨399082134660119631625687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2128438051520638035336997 399082134660119631625687)
              ·
                refine ⟨598623201990179447438531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 399082134660119631625687 598623201990179447438531)
                ·
                  refine ⟨897934802985269171157797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 598623201990179447438531 897934802985269171157797)
                  ·
                    refine ⟨168362775559737969592087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 897934802985269171157797 168362775559737969592087)
                    ·
                      rfl

theorem cell22_491828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_491828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_491828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_491828 prefixEnd_491828 := by exact prefixLift 491828
  have htrace : WordTrace (prefixWord ++ tailWord_491828) baseStart_491828 baseEnd_491828 := by
    simpa [prefixWord, tailWord_491828, baseEnd_491828] using wordTrace_append hprefix tailTrace_491828
  have hstable : (prefixWord ++ tailWord_491828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491828).length < 2 ^ (prefixWord ++ tailWord_491828).sum := by decide
  have hdescent : baseEnd_491828 < baseStart_491828 := by decide
  rcases family_descends (prefixWord ++ tailWord_491828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491916 : List Nat := [2, 2, 1, 2, 1, 4, 4, 1, 5]
def baseStart_491916 : Nat := 118140960795 + 491916 * 2 ^ 59
def prefixEnd_491916 : Nat := 4983230072969 + 3 ^ 40 * 491916 * 2
def baseEnd_491916 : Nat := 56130966586045024463939

theorem tailTrace_491916 : CollatzResearch.WordTrace tailWord_491916 prefixEnd_491916 56130966586045024463939 := by
  unfold tailWord_491916
  simp only [CollatzResearch.WordTrace]
  refine ⟨8970825242939909704663801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11961100323919879606218401 8970825242939909704663801)
  ·
    refine ⟨6728118932204932278497851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8970825242939909704663801 6728118932204932278497851)
    ·
      refine ⟨10092178398307398417746777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6728118932204932278497851 10092178398307398417746777)
      ·
        refine ⟨7569133798730548813310083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10092178398307398417746777 7569133798730548813310083)
        ·
          refine ⟨11353700698095823219965125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7569133798730548813310083 11353700698095823219965125)
          ·
            refine ⟨2128818880892966853743461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11353700698095823219965125 2128818880892966853743461)
            ·
              refine ⟨399153540167431285076899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2128818880892966853743461 399153540167431285076899)
              ·
                refine ⟨598730310251146927615349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 399153540167431285076899 598730310251146927615349)
                ·
                  refine ⟨56130966586045024463939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 598730310251146927615349 56130966586045024463939)
                  ·
                    rfl

theorem cell22_491916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 4, 1, 5].length) (baseStart_491916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_491916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_491916 prefixEnd_491916 := by exact prefixLift 491916
  have htrace : WordTrace (prefixWord ++ tailWord_491916) baseStart_491916 baseEnd_491916 := by
    simpa [prefixWord, tailWord_491916, baseEnd_491916] using wordTrace_append hprefix tailTrace_491916
  have hstable : (prefixWord ++ tailWord_491916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491916).length < 2 ^ (prefixWord ++ tailWord_491916).sum := by decide
  have hdescent : baseEnd_491916 < baseStart_491916 := by decide
  rcases family_descends (prefixWord ++ tailWord_491916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491929 : List Nat := [1, 2, 1, 2, 1, 4, 3, 1, 3, 4]
def baseStart_491929 : Nat := 118140960795 + 491929 * 2 ^ 59
def prefixEnd_491929 : Nat := 4983230072969 + 3 ^ 40 * 491929 * 2
def baseEnd_491929 : Nat := 168397349923807372816777

theorem tailTrace_491929 : CollatzResearch.WordTrace tailWord_491929 prefixEnd_491929 168397349923807372816777 := by
  unfold tailWord_491929
  simp only [CollatzResearch.WordTrace]
  refine ⟨17942124634832722629550841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11961416423221815086367227 17942124634832722629550841)
  ·
    refine ⟨13456593476124541972163131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17942124634832722629550841 13456593476124541972163131)
    ·
      refine ⟨20184890214186812958244697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13456593476124541972163131 20184890214186812958244697)
      ·
        refine ⟨15138667660640109718683523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20184890214186812958244697 15138667660640109718683523)
        ·
          refine ⟨22708001490960164578025285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15138667660640109718683523 22708001490960164578025285)
          ·
            refine ⟨4257750279555030858379741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22708001490960164578025285 4257750279555030858379741)
            ·
              refine ⟨1596656354833136571892403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4257750279555030858379741 1596656354833136571892403)
              ·
                refine ⟨2394984532249704857838605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1596656354833136571892403 2394984532249704857838605)
                ·
                  refine ⟨898119199593639321689477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2394984532249704857838605 898119199593639321689477)
                  ·
                    refine ⟨168397349923807372816777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 898119199593639321689477 168397349923807372816777)
                    ·
                      rfl

theorem cell22_491929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 3, 4].length) (baseStart_491929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_491929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_491929 prefixEnd_491929 := by exact prefixLift 491929
  have htrace : WordTrace (prefixWord ++ tailWord_491929) baseStart_491929 baseEnd_491929 := by
    simpa [prefixWord, tailWord_491929, baseEnd_491929] using wordTrace_append hprefix tailTrace_491929
  have hstable : (prefixWord ++ tailWord_491929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491929).length < 2 ^ (prefixWord ++ tailWord_491929).sum := by decide
  have hdescent : baseEnd_491929 < baseStart_491929 := by decide
  rcases family_descends (prefixWord ++ tailWord_491929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491976 : List Nat := [2, 1, 3, 1, 3, 3, 2, 1, 1, 5]
def baseStart_491976 : Nat := 118140960795 + 491976 * 2 ^ 59
def prefixEnd_491976 : Nat := 4983230072969 + 3 ^ 40 * 491976 * 2
def baseEnd_491976 : Nat := 168413438984314916891633

theorem tailTrace_491976 : CollatzResearch.WordTrace tailWord_491976 prefixEnd_491976 168413438984314916891633 := by
  unfold tailWord_491976
  simp only [CollatzResearch.WordTrace]
  refine ⟨8971919432831224828255891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11962559243774966437674521 8971919432831224828255891)
  ·
    refine ⟨13457879149246837242383837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8971919432831224828255891 13457879149246837242383837)
    ·
      refine ⟨5046704680967563965893939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13457879149246837242383837 5046704680967563965893939)
      ·
        refine ⟨7570057021451345948840909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5046704680967563965893939 7570057021451345948840909)
        ·
          refine ⟨2838771383044254730815341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7570057021451345948840909 2838771383044254730815341)
          ·
            refine ⟨1064539268641595524055753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2838771383044254730815341 1064539268641595524055753)
            ·
              refine ⟨798404451481196643041815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1064539268641595524055753 798404451481196643041815)
              ·
                refine ⟨1197606677221794964562723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 798404451481196643041815 1197606677221794964562723)
                ·
                  refine ⟨1796410015832692446844085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1197606677221794964562723 1796410015832692446844085)
                  ·
                    refine ⟨168413438984314916891633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1796410015832692446844085 168413438984314916891633)
                    ·
                      rfl

theorem cell22_491976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 1, 1, 5].length) (baseStart_491976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_491976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_491976 prefixEnd_491976 := by exact prefixLift 491976
  have htrace : WordTrace (prefixWord ++ tailWord_491976) baseStart_491976 baseEnd_491976 := by
    simpa [prefixWord, tailWord_491976, baseEnd_491976] using wordTrace_append hprefix tailTrace_491976
  have hstable : (prefixWord ++ tailWord_491976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491976).length < 2 ^ (prefixWord ++ tailWord_491976).sum := by decide
  have hdescent : baseEnd_491976 < baseStart_491976 := by decide
  rcases family_descends (prefixWord ++ tailWord_491976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492010 : List Nat := [3, 1, 3, 1, 3, 3, 1, 2, 2, 3]
def baseStart_492010 : Nat := 118140960795 + 492010 * 2 ^ 59
def prefixEnd_492010 : Nat := 4983230072969 + 3 ^ 40 * 492010 * 2
def baseEnd_492010 : Nat := 168425077879150161541529

theorem tailTrace_492010 : CollatzResearch.WordTrace tailWord_492010 prefixEnd_492010 168425077879150161541529 := by
  unfold tailWord_492010
  simp only [CollatzResearch.WordTrace]
  refine ⟨4486269736884818365812371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11963385965026182308832989 4486269736884818365812371)
  ·
    refine ⟨6729404605327227548718557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4486269736884818365812371 6729404605327227548718557)
    ·
      refine ⟨2523526726997710330769459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6729404605327227548718557 2523526726997710330769459)
      ·
        refine ⟨3785290090496565496154189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2523526726997710330769459 3785290090496565496154189)
        ·
          refine ⟨1419483783936212061057821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3785290090496565496154189 1419483783936212061057821)
          ·
            refine ⟨532306418976079522896683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1419483783936212061057821 532306418976079522896683)
            ·
              refine ⟨798459628464119284345025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 532306418976079522896683 798459628464119284345025)
              ·
                refine ⟨598844721348089463258769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 798459628464119284345025 598844721348089463258769)
                ·
                  refine ⟨449133541011067097444077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 598844721348089463258769 449133541011067097444077)
                  ·
                    refine ⟨168425077879150161541529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 449133541011067097444077 168425077879150161541529)
                    ·
                      rfl

theorem cell22_492010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_492010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_492010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_492010 prefixEnd_492010 := by exact prefixLift 492010
  have htrace : WordTrace (prefixWord ++ tailWord_492010) baseStart_492010 baseEnd_492010 := by
    simpa [prefixWord, tailWord_492010, baseEnd_492010] using wordTrace_append hprefix tailTrace_492010
  have hstable : (prefixWord ++ tailWord_492010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492010).length < 2 ^ (prefixWord ++ tailWord_492010).sum := by decide
  have hdescent : baseEnd_492010 < baseStart_492010 := by decide
  rcases family_descends (prefixWord ++ tailWord_492010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492049 : List Nat := [1, 2, 2, 1, 1, 2, 2, 2, 4, 5]
def baseStart_492049 : Nat := 118140960795 + 492049 * 2 ^ 59
def prefixEnd_492049 : Nat := 4983230072969 + 3 ^ 40 * 492049 * 2
def baseEnd_492049 : Nat := 168438428376167059816409

theorem tailTrace_492049 : CollatzResearch.WordTrace tailWord_492049 prefixEnd_492049 168438428376167059816409 := by
  unfold tailWord_492049
  simp only [CollatzResearch.WordTrace]
  refine ⟨17946501394397983123919201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11964334262931988749279467 17946501394397983123919201)
  ·
    refine ⟨13459876045798487342939401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17946501394397983123919201 13459876045798487342939401)
    ·
      refine ⟨10094907034348865507204551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13459876045798487342939401 10094907034348865507204551)
      ·
        refine ⟨15142360551523298260806827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10094907034348865507204551 15142360551523298260806827)
        ·
          refine ⟨22713540827284947391210241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15142360551523298260806827 22713540827284947391210241)
          ·
            refine ⟨17035155620463710543407681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22713540827284947391210241 17035155620463710543407681)
            ·
              refine ⟨12776366715347782907555761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17035155620463710543407681 12776366715347782907555761)
              ·
                refine ⟨9582275036510837180666821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12776366715347782907555761 9582275036510837180666821)
                ·
                  refine ⟨1796676569345781971375029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9582275036510837180666821 1796676569345781971375029)
                  ·
                    refine ⟨168438428376167059816409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1796676569345781971375029 168438428376167059816409)
                    ·
                      rfl

theorem cell22_492049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 5].length) (baseStart_492049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_492049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_492049 prefixEnd_492049 := by exact prefixLift 492049
  have htrace : WordTrace (prefixWord ++ tailWord_492049) baseStart_492049 baseEnd_492049 := by
    simpa [prefixWord, tailWord_492049, baseEnd_492049] using wordTrace_append hprefix tailTrace_492049
  have hstable : (prefixWord ++ tailWord_492049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492049).length < 2 ^ (prefixWord ++ tailWord_492049).sum := by decide
  have hdescent : baseEnd_492049 < baseStart_492049 := by decide
  rcases family_descends (prefixWord ++ tailWord_492049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492111 : List Nat := [1, 1, 2, 1, 1, 2, 4, 1, 6, 3]
def baseStart_492111 : Nat := 118140960795 + 492111 * 2 ^ 59
def prefixEnd_492111 : Nat := 4983230072969 + 3 ^ 40 * 492111 * 2
def baseEnd_492111 : Nat := 168459652243219564766219

theorem tailTrace_492111 : CollatzResearch.WordTrace tailWord_492111 prefixEnd_492111 168459652243219564766219 := by
  unfold tailWord_492111
  simp only [CollatzResearch.WordTrace]
  refine ⟨17948762720173367712676187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11965841813448911808450791 17948762720173367712676187)
  ·
    refine ⟨26923144080260051569014281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17948762720173367712676187 26923144080260051569014281)
    ·
      refine ⟨20192358060195038676760711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26923144080260051569014281 20192358060195038676760711)
      ·
        refine ⟨30288537090292558015141067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20192358060195038676760711 30288537090292558015141067)
        ·
          refine ⟨45432805635438837022711601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30288537090292558015141067 45432805635438837022711601)
          ·
            refine ⟨34074604226579127767033701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45432805635438837022711601 34074604226579127767033701)
            ·
              refine ⟨6388988292483586456318819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34074604226579127767033701 6388988292483586456318819)
              ·
                refine ⟨9583482438725379684478229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6388988292483586456318819 9583482438725379684478229)
                ·
                  refine ⟨449225739315252172709917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9583482438725379684478229 449225739315252172709917)
                  ·
                    refine ⟨168459652243219564766219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 449225739315252172709917 168459652243219564766219)
                    ·
                      rfl

theorem cell22_492111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 6, 3].length) (baseStart_492111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_492111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_492111 prefixEnd_492111 := by exact prefixLift 492111
  have htrace : WordTrace (prefixWord ++ tailWord_492111) baseStart_492111 baseEnd_492111 := by
    simpa [prefixWord, tailWord_492111, baseEnd_492111] using wordTrace_append hprefix tailTrace_492111
  have hstable : (prefixWord ++ tailWord_492111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492111).length < 2 ^ (prefixWord ++ tailWord_492111).sum := by decide
  have hdescent : baseEnd_492111 < baseStart_492111 := by decide
  rcases family_descends (prefixWord ++ tailWord_492111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492128 : List Nat := [2, 1, 1, 3, 2, 1, 3, 4, 2, 3]
def baseStart_492128 : Nat := 118140960795 + 492128 * 2 ^ 59
def prefixEnd_492128 : Nat := 4983230072969 + 3 ^ 40 * 492128 * 2
def baseEnd_492128 : Nat := 168465471690637187091167

theorem tailTrace_492128 : CollatzResearch.WordTrace tailWord_492128 prefixEnd_492128 168465471690637187091167 := by
  unfold tailWord_492128
  simp only [CollatzResearch.WordTrace]
  refine ⟨8974691380555889808022519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11966255174074519744030025 8974691380555889808022519)
  ·
    refine ⟨13462037070833834712033779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8974691380555889808022519 13462037070833834712033779)
    ·
      refine ⟨20193055606250752068050669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13462037070833834712033779 20193055606250752068050669)
      ·
        refine ⟨7572395852344032025519001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20193055606250752068050669 7572395852344032025519001)
        ·
          refine ⟨5679296889258024019139251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7572395852344032025519001 5679296889258024019139251)
          ·
            refine ⟨8518945333887036028708877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5679296889258024019139251 8518945333887036028708877)
            ·
              refine ⟨3194604500207638510765829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8518945333887036028708877 3194604500207638510765829)
              ·
                refine ⟨598988343788932220768593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3194604500207638510765829 598988343788932220768593)
                ·
                  refine ⟨449241257841699165576445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 598988343788932220768593 449241257841699165576445)
                  ·
                    refine ⟨168465471690637187091167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 449241257841699165576445 168465471690637187091167)
                    ·
                      rfl

theorem cell22_492128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 4, 2, 3].length) (baseStart_492128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_492128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_492128 prefixEnd_492128 := by exact prefixLift 492128
  have htrace : WordTrace (prefixWord ++ tailWord_492128) baseStart_492128 baseEnd_492128 := by
    simpa [prefixWord, tailWord_492128, baseEnd_492128] using wordTrace_append hprefix tailTrace_492128
  have hstable : (prefixWord ++ tailWord_492128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492128).length < 2 ^ (prefixWord ++ tailWord_492128).sum := by decide
  have hdescent : baseEnd_492128 < baseStart_492128 := by decide
  rcases family_descends (prefixWord ++ tailWord_492128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492248 : List Nat := [2, 1, 2, 2, 3, 2, 3, 1, 6]
def baseStart_492248 : Nat := 118140960795 + 492248 * 2 ^ 59
def prefixEnd_492248 : Nat := 4983230072969 + 3 ^ 40 * 492248 * 2
def baseEnd_492248 : Nat := 56168850047665624696933

theorem tailTrace_492248 : CollatzResearch.WordTrace tailWord_492248 prefixEnd_492248 56168850047665624696933 := by
  unfold tailWord_492248
  simp only [CollatzResearch.WordTrace]
  refine ⟨8976879760338520055206699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11969173013784693406942265 8976879760338520055206699)
  ·
    refine ⟨13465319640507780082810049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8976879760338520055206699 13465319640507780082810049)
    ·
      refine ⟨10098989730380835062107537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13465319640507780082810049 10098989730380835062107537)
      ·
        refine ⟨7574242297785626296580653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10098989730380835062107537 7574242297785626296580653)
        ·
          refine ⟨2840340861669609861217745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7574242297785626296580653 2840340861669609861217745)
          ·
            refine ⟨2130255646252207395913309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2840340861669609861217745 2130255646252207395913309)
            ·
              refine ⟨798845867344577773467491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2130255646252207395913309 798845867344577773467491)
              ·
                refine ⟨1198268801016866660201237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 798845867344577773467491 1198268801016866660201237)
                ·
                  refine ⟨56168850047665624696933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1198268801016866660201237 56168850047665624696933)
                  ·
                    rfl

theorem cell22_492248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 1, 6].length) (baseStart_492248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_492248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_492248 prefixEnd_492248 := by exact prefixLift 492248
  have htrace : WordTrace (prefixWord ++ tailWord_492248) baseStart_492248 baseEnd_492248 := by
    simpa [prefixWord, tailWord_492248, baseEnd_492248] using wordTrace_append hprefix tailTrace_492248
  have hstable : (prefixWord ++ tailWord_492248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492248).length < 2 ^ (prefixWord ++ tailWord_492248).sum := by decide
  have hdescent : baseEnd_492248 < baseStart_492248 := by decide
  rcases family_descends (prefixWord ++ tailWord_492248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492295 : List Nat := [1, 1, 4, 4, 1, 1, 2, 2, 2, 4]
def baseStart_492295 : Nat := 118140960795 + 492295 * 2 ^ 59
def prefixEnd_492295 : Nat := 4983230072969 + 3 ^ 40 * 492295 * 2
def baseEnd_492295 : Nat := 168522639203504418165655

theorem tailTrace_492295 : CollatzResearch.WordTrace tailWord_492295 prefixEnd_492295 168522639203504418165655 := by
  unfold tailWord_492295
  simp only [CollatzResearch.WordTrace]
  refine ⟨17955473751506767137374339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11970315834337844758249559 17955473751506767137374339)
  ·
    refine ⟨26933210627260150706061509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17955473751506767137374339 26933210627260150706061509)
    ·
      refine ⟨5049976992611278257386533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26933210627260150706061509 5049976992611278257386533)
      ·
        refine ⟨946870686114614673259975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5049976992611278257386533 946870686114614673259975)
        ·
          refine ⟨1420306029171922009889963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 946870686114614673259975 1420306029171922009889963)
          ·
            refine ⟨2130459043757883014834945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1420306029171922009889963 2130459043757883014834945)
            ·
              refine ⟨1597844282818412261126209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2130459043757883014834945 1597844282818412261126209)
              ·
                refine ⟨1198383212113809195844657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1597844282818412261126209 1198383212113809195844657)
                ·
                  refine ⟨898787409085356896883493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1198383212113809195844657 898787409085356896883493)
                  ·
                    refine ⟨168522639203504418165655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 898787409085356896883493 168522639203504418165655)
                    ·
                      rfl

theorem cell22_492295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_492295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_492295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_492295 prefixEnd_492295 := by exact prefixLift 492295
  have htrace : WordTrace (prefixWord ++ tailWord_492295) baseStart_492295 baseEnd_492295 := by
    simpa [prefixWord, tailWord_492295, baseEnd_492295] using wordTrace_append hprefix tailTrace_492295
  have hstable : (prefixWord ++ tailWord_492295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492295).length < 2 ^ (prefixWord ++ tailWord_492295).sum := by decide
  have hdescent : baseEnd_492295 < baseStart_492295 := by decide
  rcases family_descends (prefixWord ++ tailWord_492295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492325 : List Nat := [1, 3, 1, 2, 3, 1, 3, 2, 3, 3]
def baseStart_492325 : Nat := 118140960795 + 492325 * 2 ^ 59
def prefixEnd_492325 : Nat := 4983230072969 + 3 ^ 40 * 492325 * 2
def baseEnd_492325 : Nat := 168532908816594339915563

theorem tailTrace_492325 : CollatzResearch.WordTrace tailWord_492325 prefixEnd_492325 168532908816594339915563 := by
  unfold tailWord_492325
  simp only [CollatzResearch.WordTrace]
  refine ⟨17956567941398082260966429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11971045294265388173977619 17956567941398082260966429)
  ·
    refine ⟨6733712978024280847862411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17956567941398082260966429 6733712978024280847862411)
    ·
      refine ⟨10100569467036421271793617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6733712978024280847862411 10100569467036421271793617)
      ·
        refine ⟨7575427100277315953845213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10100569467036421271793617 7575427100277315953845213)
        ·
          refine ⟨2840785162603993482691955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7575427100277315953845213 2840785162603993482691955)
          ·
            refine ⟨4261177743905990224037933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2840785162603993482691955 4261177743905990224037933)
            ·
              refine ⟨1597941653964746334014225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4261177743905990224037933 1597941653964746334014225)
              ·
                refine ⟨1198456240473559750510669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1597941653964746334014225 1198456240473559750510669)
                ·
                  refine ⟨449421090177584906441501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1198456240473559750510669 449421090177584906441501)
                  ·
                    refine ⟨168532908816594339915563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 449421090177584906441501 168532908816594339915563)
                    ·
                      rfl

theorem cell22_492325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 2, 3, 3].length) (baseStart_492325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_492325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_492325 prefixEnd_492325 := by exact prefixLift 492325
  have htrace : WordTrace (prefixWord ++ tailWord_492325) baseStart_492325 baseEnd_492325 := by
    simpa [prefixWord, tailWord_492325, baseEnd_492325] using wordTrace_append hprefix tailTrace_492325
  have hstable : (prefixWord ++ tailWord_492325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492325).length < 2 ^ (prefixWord ++ tailWord_492325).sum := by decide
  have hdescent : baseEnd_492325 < baseStart_492325 := by decide
  rcases family_descends (prefixWord ++ tailWord_492325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492338 : List Nat := [3, 2, 1, 1, 3, 1, 2, 2, 7]
def baseStart_492338 : Nat := 118140960795 + 492338 * 2 ^ 59
def prefixEnd_492338 : Nat := 4983230072969 + 3 ^ 40 * 492338 * 2
def baseEnd_492338 : Nat := 56179119660755546446841

theorem tailTrace_492338 : CollatzResearch.WordTrace tailWord_492338 prefixEnd_492338 56179119660755546446841 := by
  unfold tailWord_492338
  simp only [CollatzResearch.WordTrace]
  refine ⟨4489260522587746370297417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11971361393567323654126445 4489260522587746370297417)
  ·
    refine ⟨3366945391940809777723063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4489260522587746370297417 3366945391940809777723063)
    ·
      refine ⟨5050418087911214666584595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3366945391940809777723063 5050418087911214666584595)
      ·
        refine ⟨7575627131866821999876893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5050418087911214666584595 7575627131866821999876893)
        ·
          refine ⟨2840860174450058249953835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7575627131866821999876893 2840860174450058249953835)
          ·
            refine ⟨4261290261675087374930753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2840860174450058249953835 4261290261675087374930753)
            ·
              refine ⟨3195967696256315531198065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4261290261675087374930753 3195967696256315531198065)
              ·
                refine ⟨2396975772192236648398549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3195967696256315531198065 2396975772192236648398549)
                ·
                  refine ⟨56179119660755546446841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2396975772192236648398549 56179119660755546446841)
                  ·
                    rfl

theorem cell22_492338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 7].length) (baseStart_492338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_492338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_492338 prefixEnd_492338 := by exact prefixLift 492338
  have htrace : WordTrace (prefixWord ++ tailWord_492338) baseStart_492338 baseEnd_492338 := by
    simpa [prefixWord, tailWord_492338, baseEnd_492338] using wordTrace_append hprefix tailTrace_492338
  have hstable : (prefixWord ++ tailWord_492338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492338).length < 2 ^ (prefixWord ++ tailWord_492338).sum := by decide
  have hdescent : baseEnd_492338 < baseStart_492338 := by decide
  rcases family_descends (prefixWord ++ tailWord_492338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492368 : List Nat := [2, 1, 1, 1, 1, 4, 2, 1, 5, 4]
def baseStart_492368 : Nat := 118140960795 + 492368 * 2 ^ 59
def prefixEnd_492368 : Nat := 4983230072969 + 3 ^ 40 * 492368 * 2
def baseEnd_492368 : Nat := 168547628595356561090431

theorem tailTrace_492368 : CollatzResearch.WordTrace tailWord_492368 prefixEnd_492368 168547628595356561090431 := by
  unfold tailWord_492368
  simp only [CollatzResearch.WordTrace]
  refine ⟨8979068140121150302390879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11972090853494867069854505 8979068140121150302390879)
  ·
    refine ⟨13468602210181725453586319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8979068140121150302390879 13468602210181725453586319)
    ·
      refine ⟨20202903315272588180379479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13468602210181725453586319 20202903315272588180379479)
      ·
        refine ⟨30304354972908882270569219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20202903315272588180379479 30304354972908882270569219)
        ·
          refine ⟨45456532459363323405853829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30304354972908882270569219 45456532459363323405853829)
          ·
            refine ⟨8523099836130623138597593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45456532459363323405853829 8523099836130623138597593)
            ·
              refine ⟨6392324877097967353948195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8523099836130623138597593 6392324877097967353948195)
              ·
                refine ⟨9588487315646951030922293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6392324877097967353948195 9588487315646951030922293)
                ·
                  refine ⟨898920685841901659148965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9588487315646951030922293 898920685841901659148965)
                  ·
                    refine ⟨168547628595356561090431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 898920685841901659148965 168547628595356561090431)
                    ·
                      rfl

theorem cell22_492368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 5, 4].length) (baseStart_492368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_492368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_492368 prefixEnd_492368 := by exact prefixLift 492368
  have htrace : WordTrace (prefixWord ++ tailWord_492368) baseStart_492368 baseEnd_492368 := by
    simpa [prefixWord, tailWord_492368, baseEnd_492368] using wordTrace_append hprefix tailTrace_492368
  have hstable : (prefixWord ++ tailWord_492368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492368).length < 2 ^ (prefixWord ++ tailWord_492368).sum := by decide
  have hdescent : baseEnd_492368 < baseStart_492368 := by decide
  rcases family_descends (prefixWord ++ tailWord_492368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492383 : List Nat := [1, 1, 2, 3, 1, 3, 1, 4, 6]
def baseStart_492383 : Nat := 118140960795 + 492383 * 2 ^ 59
def prefixEnd_492383 : Nat := 4983230072969 + 3 ^ 40 * 492383 * 2
def baseEnd_492383 : Nat := 56184254467300507321795

theorem tailTrace_492383 : CollatzResearch.WordTrace tailWord_492383 prefixEnd_492383 56184254467300507321795 := by
  unfold tailWord_492383
  simp only [CollatzResearch.WordTrace]
  refine ⟨17958683375187958166577803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11972455583458638777718535 17958683375187958166577803)
  ·
    refine ⟨26938025062781937249866705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17958683375187958166577803 26938025062781937249866705)
    ·
      refine ⟨20203518797086452937400029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26938025062781937249866705 20203518797086452937400029)
      ·
        refine ⟨7576319548907419851525011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20203518797086452937400029 7576319548907419851525011)
        ·
          refine ⟨11364479323361129777287517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7576319548907419851525011 11364479323361129777287517)
          ·
            refine ⟨4261679746260423666482819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11364479323361129777287517 4261679746260423666482819)
            ·
              refine ⟨6392519619390635499724229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4261679746260423666482819 6392519619390635499724229)
              ·
                refine ⟨1198597428635744156198293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6392519619390635499724229 1198597428635744156198293)
                ·
                  refine ⟨56184254467300507321795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1198597428635744156198293 56184254467300507321795)
                  ·
                    rfl

theorem cell22_492383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 4, 6].length) (baseStart_492383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_492383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_492383 prefixEnd_492383 := by exact prefixLift 492383
  have htrace : WordTrace (prefixWord ++ tailWord_492383) baseStart_492383 baseEnd_492383 := by
    simpa [prefixWord, tailWord_492383, baseEnd_492383] using wordTrace_append hprefix tailTrace_492383
  have hstable : (prefixWord ++ tailWord_492383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492383).length < 2 ^ (prefixWord ++ tailWord_492383).sum := by decide
  have hdescent : baseEnd_492383 < baseStart_492383 := by decide
  rcases family_descends (prefixWord ++ tailWord_492383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492415 : List Nat := [1, 1, 2, 2, 1, 1, 6, 1, 4, 3]
def baseStart_492415 : Nat := 118140960795 + 492415 * 2 ^ 59
def prefixEnd_492415 : Nat := 4983230072969 + 3 ^ 40 * 492415 * 2
def baseEnd_492415 : Nat := 168563717655864105165287

theorem tailTrace_492415 : CollatzResearch.WordTrace tailWord_492415 prefixEnd_492415 168563717655864105165287 := by
  unfold tailWord_492415
  simp only [CollatzResearch.WordTrace]
  refine ⟨17959850511072027631742699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11973233674048018421161799 17959850511072027631742699)
  ·
    refine ⟨26939775766608041447614049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17959850511072027631742699 26939775766608041447614049)
    ·
      refine ⟨20204831824956031085710537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26939775766608041447614049 20204831824956031085710537)
      ·
        refine ⟨15153623868717023314282903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20204831824956031085710537 15153623868717023314282903)
        ·
          refine ⟨22730435803075534971424355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15153623868717023314282903 22730435803075534971424355)
          ·
            refine ⟨34095653704613302457136533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22730435803075534971424355 34095653704613302457136533)
            ·
              refine ⟨1598233767403748552678275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34095653704613302457136533 1598233767403748552678275)
              ·
                refine ⟨2397350651105622829017413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1598233767403748552678275 2397350651105622829017413)
                ·
                  refine ⟨449503247082304280440765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2397350651105622829017413 449503247082304280440765)
                  ·
                    refine ⟨168563717655864105165287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 449503247082304280440765 168563717655864105165287)
                    ·
                      rfl

theorem cell22_492415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 4, 3].length) (baseStart_492415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_492415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_492415 prefixEnd_492415 := by exact prefixLift 492415
  have htrace : WordTrace (prefixWord ++ tailWord_492415) baseStart_492415 baseEnd_492415 := by
    simpa [prefixWord, tailWord_492415, baseEnd_492415] using wordTrace_append hprefix tailTrace_492415
  have hstable : (prefixWord ++ tailWord_492415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492415).length < 2 ^ (prefixWord ++ tailWord_492415).sum := by decide
  have hdescent : baseEnd_492415 < baseStart_492415 := by decide
  rcases family_descends (prefixWord ++ tailWord_492415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492428 : List Nat := [2, 2, 1, 2, 1, 2, 3, 9]
def baseStart_492428 : Nat := 118140960795 + 492428 * 2 ^ 59
def prefixEnd_492428 : Nat := 4983230072969 + 3 ^ 40 * 492428 * 2
def baseEnd_492428 : Nat := 18729796424615156065583

theorem tailTrace_492428 : CollatzResearch.WordTrace tailWord_492428 prefixEnd_492428 18729796424615156065583 := by
  unfold tailWord_492428
  simp only [CollatzResearch.WordTrace]
  refine ⟨8980162330012465425982969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11973549773349953901310625 8980162330012465425982969)
  ·
    refine ⟨6735121747509349069487227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8980162330012465425982969 6735121747509349069487227)
    ·
      refine ⟨10102682621264023604230841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6735121747509349069487227 10102682621264023604230841)
      ·
        refine ⟨7577011965948017703173131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10102682621264023604230841 7577011965948017703173131)
        ·
          refine ⟨11365517948922026554759697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7577011965948017703173131 11365517948922026554759697)
          ·
            refine ⟨8524138461691519916069773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11365517948922026554759697 8524138461691519916069773)
            ·
              refine ⟨3196551923134319968526165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8524138461691519916069773 3196551923134319968526165)
              ·
                refine ⟨18729796424615156065583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3196551923134319968526165 18729796424615156065583)
                ·
                  rfl

theorem cell22_492428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 9].length) (baseStart_492428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_492428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_492428 prefixEnd_492428 := by exact prefixLift 492428
  have htrace : WordTrace (prefixWord ++ tailWord_492428) baseStart_492428 baseEnd_492428 := by
    simpa [prefixWord, tailWord_492428, baseEnd_492428] using wordTrace_append hprefix tailTrace_492428
  have hstable : (prefixWord ++ tailWord_492428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492428).length < 2 ^ (prefixWord ++ tailWord_492428).sum := by decide
  have hdescent : baseEnd_492428 < baseStart_492428 := by decide
  rcases family_descends (prefixWord ++ tailWord_492428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492447 : List Nat := [1, 1, 2, 5, 2, 2, 2, 1, 2, 4]
def baseStart_492447 : Nat := 118140960795 + 492447 * 2 ^ 59
def prefixEnd_492447 : Nat := 4983230072969 + 3 ^ 40 * 492447 * 2
def baseEnd_492447 : Nat := 168574671909826688365189

theorem tailTrace_492447 : CollatzResearch.WordTrace tailWord_492447 prefixEnd_492447 168574671909826688365189 := by
  unfold tailWord_492447
  simp only [CollatzResearch.WordTrace]
  refine ⟨17961017646956097096907595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11974011764637398064605063 17961017646956097096907595)
  ·
    refine ⟨26941526470434145645361393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17961017646956097096907595 26941526470434145645361393)
    ·
      refine ⟨20206144852825609234021045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26941526470434145645361393 20206144852825609234021045)
      ·
        refine ⟨1894326079952400865689473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20206144852825609234021045 1894326079952400865689473)
        ·
          refine ⟨1420744559964300649267105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1894326079952400865689473 1420744559964300649267105)
          ·
            refine ⟨1065558419973225486950329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1420744559964300649267105 1065558419973225486950329)
            ·
              refine ⟨799168814979919115212747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1065558419973225486950329 799168814979919115212747)
              ·
                refine ⟨1198753222469878672819121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 799168814979919115212747 1198753222469878672819121)
                ·
                  refine ⟨899064916852409004614341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1198753222469878672819121 899064916852409004614341)
                  ·
                    refine ⟨168574671909826688365189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 899064916852409004614341 168574671909826688365189)
                    ·
                      rfl

theorem cell22_492447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 1, 2, 4].length) (baseStart_492447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_492447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_492447 prefixEnd_492447 := by exact prefixLift 492447
  have htrace : WordTrace (prefixWord ++ tailWord_492447) baseStart_492447 baseEnd_492447 := by
    simpa [prefixWord, tailWord_492447, baseEnd_492447] using wordTrace_append hprefix tailTrace_492447
  have hstable : (prefixWord ++ tailWord_492447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492447).length < 2 ^ (prefixWord ++ tailWord_492447).sum := by decide
  have hdescent : baseEnd_492447 < baseStart_492447 := by decide
  rcases family_descends (prefixWord ++ tailWord_492447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492460 : List Nat := [2, 2, 1, 1, 1, 1, 2, 4, 5, 3]
def baseStart_492460 : Nat := 118140960795 + 492460 * 2 ^ 59
def prefixEnd_492460 : Nat := 4983230072969 + 3 ^ 40 * 492460 * 2
def baseEnd_492460 : Nat := 168579122075498987790149

theorem tailTrace_492460 : CollatzResearch.WordTrace tailWord_492460 prefixEnd_492460 168579122075498987790149 := by
  unfold tailWord_492460
  simp only [CollatzResearch.WordTrace]
  refine ⟨8980745897954500158565417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11974327863939333544753889 8980745897954500158565417)
  ·
    refine ⟨6735559423465875118924063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8980745897954500158565417 6735559423465875118924063)
    ·
      refine ⟨10103339135198812678386095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6735559423465875118924063 10103339135198812678386095)
      ·
        refine ⟨15155008702798219017579143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10103339135198812678386095 15155008702798219017579143)
        ·
          refine ⟨22732513054197328526368715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15155008702798219017579143 22732513054197328526368715)
          ·
            refine ⟨34098769581295992789553073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22732513054197328526368715 34098769581295992789553073)
            ·
              refine ⟨25574077185971994592164805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34098769581295992789553073 25574077185971994592164805)
              ·
                refine ⟨4795139472369748986030901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25574077185971994592164805 4795139472369748986030901)
                ·
                  refine ⟨449544325534663967440397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4795139472369748986030901 449544325534663967440397)
                  ·
                    refine ⟨168579122075498987790149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 449544325534663967440397 168579122075498987790149)
                    ·
                      rfl

theorem cell22_492460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 3].length) (baseStart_492460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_492460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_492460 prefixEnd_492460 := by exact prefixLift 492460
  have htrace : WordTrace (prefixWord ++ tailWord_492460) baseStart_492460 baseEnd_492460 := by
    simpa [prefixWord, tailWord_492460, baseEnd_492460] using wordTrace_append hprefix tailTrace_492460
  have hstable : (prefixWord ++ tailWord_492460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492460).length < 2 ^ (prefixWord ++ tailWord_492460).sum := by decide
  have hdescent : baseEnd_492460 < baseStart_492460 := by decide
  rcases family_descends (prefixWord ++ tailWord_492460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492468 : List Nat := [2, 5, 2, 1, 1, 3, 2, 2, 4]
def baseStart_492468 : Nat := 118140960795 + 492468 * 2 ^ 59
def prefixEnd_492468 : Nat := 4983230072969 + 3 ^ 40 * 492468 * 2
def baseEnd_492468 : Nat := 56193953546329877863375

theorem tailTrace_492468 : CollatzResearch.WordTrace tailWord_492468 prefixEnd_492468 56193953546329877863375 := by
  unfold tailWord_492468
  simp only [CollatzResearch.WordTrace]
  refine ⟨8980891789940008841711029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11974522386586678455614705 8980891789940008841711029)
  ·
    refine ⟨841958605306875828910409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8980891789940008841711029 841958605306875828910409)
    ·
      refine ⟨631468953980156871682807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 841958605306875828910409 631468953980156871682807)
      ·
        refine ⟨947203430970235307524211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 631468953980156871682807 947203430970235307524211)
        ·
          refine ⟨1420805146455352961286317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 947203430970235307524211 1420805146455352961286317)
          ·
            refine ⟨532801929920757360482369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1420805146455352961286317 532801929920757360482369)
            ·
              refine ⟨399601447440568020361777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 532801929920757360482369 399601447440568020361777)
              ·
                refine ⟨299701085580426015271333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 399601447440568020361777 299701085580426015271333)
                ·
                  refine ⟨56193953546329877863375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 299701085580426015271333 56193953546329877863375)
                  ·
                    rfl

theorem cell22_492468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_492468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_492468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_492468 prefixEnd_492468 := by exact prefixLift 492468
  have htrace : WordTrace (prefixWord ++ tailWord_492468) baseStart_492468 baseEnd_492468 := by
    simpa [prefixWord, tailWord_492468, baseEnd_492468] using wordTrace_append hprefix tailTrace_492468
  have hstable : (prefixWord ++ tailWord_492468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492468).length < 2 ^ (prefixWord ++ tailWord_492468).sum := by decide
  have hdescent : baseEnd_492468 < baseStart_492468 := by decide
  rcases family_descends (prefixWord ++ tailWord_492468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492511 : List Nat := [1, 1, 2, 3, 5, 1, 2, 3, 1, 3]
def baseStart_492511 : Nat := 118140960795 + 492511 * 2 ^ 59
def prefixEnd_492511 : Nat := 4983230072969 + 3 ^ 40 * 492511 * 2
def baseEnd_492511 : Nat := 168596580417751854764993

theorem tailTrace_492511 : CollatzResearch.WordTrace tailWord_492511 prefixEnd_492511 168596580417751854764993 := by
  unfold tailWord_492511
  simp only [CollatzResearch.WordTrace]
  refine ⟨17963351918724236027237387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11975567945816157351491591 17963351918724236027237387)
  ·
    refine ⟨26945027878086354040856081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17963351918724236027237387 26945027878086354040856081)
    ·
      refine ⟨20208770908564765530642061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26945027878086354040856081 20208770908564765530642061)
      ·
        refine ⟨7578289090711787073990773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20208770908564765530642061 7578289090711787073990773)
        ·
          refine ⟨710464602254230038186635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7578289090711787073990773 710464602254230038186635)
          ·
            refine ⟨1065696903381345057279953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 710464602254230038186635 1065696903381345057279953)
            ·
              refine ⟨799272677536008792959965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1065696903381345057279953 799272677536008792959965)
              ·
                refine ⟨299727254076003297359987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 799272677536008792959965 299727254076003297359987)
                ·
                  refine ⟨449590881114004946039981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 299727254076003297359987 449590881114004946039981)
                  ·
                    refine ⟨168596580417751854764993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 449590881114004946039981 168596580417751854764993)
                    ·
                      rfl

theorem cell22_492511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 3, 1, 3].length) (baseStart_492511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_492511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_492511 prefixEnd_492511 := by exact prefixLift 492511
  have htrace : WordTrace (prefixWord ++ tailWord_492511) baseStart_492511 baseEnd_492511 := by
    simpa [prefixWord, tailWord_492511, baseEnd_492511] using wordTrace_append hprefix tailTrace_492511
  have hstable : (prefixWord ++ tailWord_492511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492511).length < 2 ^ (prefixWord ++ tailWord_492511).sum := by decide
  have hdescent : baseEnd_492511 < baseStart_492511 := by decide
  rcases family_descends (prefixWord ++ tailWord_492511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492554 : List Nat := [3, 1, 2, 2, 3, 2, 2, 2, 1, 4]
def baseStart_492554 : Nat := 118140960795 + 492554 * 2 ^ 59
def prefixEnd_492554 : Nat := 4983230072969 + 3 ^ 40 * 492554 * 2
def baseEnd_492554 : Nat := 168611300196514075939861

theorem tailTrace_492554 : CollatzResearch.WordTrace tailWord_492554 prefixEnd_492554 168611300196514075939861 := by
  unfold tailWord_492554
  simp only [CollatzResearch.WordTrace]
  refine ⟨4491230064392113592763179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11976613505045636247368477 4491230064392113592763179)
  ·
    refine ⟨6736845096588170389144769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4491230064392113592763179 6736845096588170389144769)
    ·
      refine ⟨5052633822441127791858577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6736845096588170389144769 5052633822441127791858577)
      ·
        refine ⟨3789475366830845843893933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5052633822441127791858577 3789475366830845843893933)
        ·
          refine ⟨1421053262561567191460225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3789475366830845843893933 1421053262561567191460225)
          ·
            refine ⟨1065789946921175393595169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1421053262561567191460225 1065789946921175393595169)
            ·
              refine ⟨799342460190881545196377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1065789946921175393595169 799342460190881545196377)
              ·
                refine ⟨599506845143161158897283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 799342460190881545196377 599506845143161158897283)
                ·
                  refine ⟨899260267714741738345925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 599506845143161158897283 899260267714741738345925)
                  ·
                    refine ⟨168611300196514075939861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 899260267714741738345925 168611300196514075939861)
                    ·
                      rfl

theorem cell22_492554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 2, 1, 4].length) (baseStart_492554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_492554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_492554 prefixEnd_492554 := by exact prefixLift 492554
  have htrace : WordTrace (prefixWord ++ tailWord_492554) baseStart_492554 baseEnd_492554 := by
    simpa [prefixWord, tailWord_492554, baseEnd_492554] using wordTrace_append hprefix tailTrace_492554
  have hstable : (prefixWord ++ tailWord_492554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492554).length < 2 ^ (prefixWord ++ tailWord_492554).sum := by decide
  have hdescent : baseEnd_492554 < baseStart_492554 := by decide
  rcases family_descends (prefixWord ++ tailWord_492554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492562 : List Nat := [3, 2, 5, 1, 1, 2, 1, 3, 1, 3]
def baseStart_492562 : Nat := 118140960795 + 492562 * 2 ^ 59
def prefixEnd_492562 : Nat := 4983230072969 + 3 ^ 40 * 492562 * 2
def baseEnd_492562 : Nat := 168614038760004721739837

theorem tailTrace_492562 : CollatzResearch.WordTrace tailWord_492562 prefixEnd_492562 168614038760004721739837 := by
  unfold tailWord_492562
  simp only [CollatzResearch.WordTrace]
  refine ⟨4491303010384867934335985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11976808027692981158229293 4491303010384867934335985)
  ·
    refine ⟨3368477257788650950751989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4491303010384867934335985 3368477257788650950751989)
    ·
      refine ⟨315794742917686026632999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3368477257788650950751989 315794742917686026632999)
      ·
        refine ⟨473692114376529039949499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315794742917686026632999 473692114376529039949499)
        ·
          refine ⟨710538171564793559924249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473692114376529039949499 710538171564793559924249)
          ·
            refine ⟨532903628673595169943187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 710538171564793559924249 532903628673595169943187)
            ·
              refine ⟨799355443010392754914781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 532903628673595169943187 799355443010392754914781)
              ·
                refine ⟨299758291128897283093043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 799355443010392754914781 299758291128897283093043)
                ·
                  refine ⟨449637436693345924639565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 299758291128897283093043 449637436693345924639565)
                  ·
                    refine ⟨168614038760004721739837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 449637436693345924639565 168614038760004721739837)
                    ·
                      rfl

theorem cell22_492562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_492562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_492562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_492562 prefixEnd_492562 := by exact prefixLift 492562
  have htrace : WordTrace (prefixWord ++ tailWord_492562) baseStart_492562 baseEnd_492562 := by
    simpa [prefixWord, tailWord_492562, baseEnd_492562] using wordTrace_append hprefix tailTrace_492562
  have hstable : (prefixWord ++ tailWord_492562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492562).length < 2 ^ (prefixWord ++ tailWord_492562).sum := by decide
  have hdescent : baseEnd_492562 < baseStart_492562 := by decide
  rcases family_descends (prefixWord ++ tailWord_492562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492586 : List Nat := [3, 1, 4, 1, 4, 1, 1, 1, 6]
def baseStart_492586 : Nat := 118140960795 + 492586 * 2 ^ 59
def prefixEnd_492586 : Nat := 4983230072969 + 3 ^ 40 * 492586 * 2
def baseEnd_492586 : Nat := 56207418150158886379921

theorem tailTrace_492586 : CollatzResearch.WordTrace tailWord_492586 prefixEnd_492586 56207418150158886379921 := by
  unfold tailWord_492586
  simp only [CollatzResearch.WordTrace]
  refine ⟨4491521848363130959054403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11977391595635015890811741 4491521848363130959054403)
  ·
    refine ⟨6737282772544696438581605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4491521848363130959054403 6737282772544696438581605)
    ·
      refine ⟨1263240519852130582234051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6737282772544696438581605 1263240519852130582234051)
      ·
        refine ⟨1894860779778195873351077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1263240519852130582234051 1894860779778195873351077)
        ·
          refine ⟨355286396208411726253327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1894860779778195873351077 355286396208411726253327)
          ·
            refine ⟨532929594312617589379991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355286396208411726253327 532929594312617589379991)
            ·
              refine ⟨799394391468926384069987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 532929594312617589379991 799394391468926384069987)
              ·
                refine ⟨1199091587203389576104981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 799394391468926384069987 1199091587203389576104981)
                ·
                  refine ⟨56207418150158886379921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1199091587203389576104981 56207418150158886379921)
                  ·
                    rfl

theorem cell22_492586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 1, 6].length) (baseStart_492586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_492586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_492586 prefixEnd_492586 := by exact prefixLift 492586
  have htrace : WordTrace (prefixWord ++ tailWord_492586) baseStart_492586 baseEnd_492586 := by
    simpa [prefixWord, tailWord_492586, baseEnd_492586] using wordTrace_append hprefix tailTrace_492586
  have hstable : (prefixWord ++ tailWord_492586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492586).length < 2 ^ (prefixWord ++ tailWord_492586).sum := by decide
  have hdescent : baseEnd_492586 < baseStart_492586 := by decide
  rcases family_descends (prefixWord ++ tailWord_492586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492601 : List Nat := [1, 2, 1, 5, 2, 1, 4, 1, 2, 3]
def baseStart_492601 : Nat := 118140960795 + 492601 * 2 ^ 59
def prefixEnd_492601 : Nat := 4983230072969 + 3 ^ 40 * 492601 * 2
def baseEnd_492601 : Nat := 168627389257021620014717

theorem tailTrace_492601 : CollatzResearch.WordTrace tailWord_492601 prefixEnd_492601 168627389257021620014717 := by
  unfold tailWord_492601
  simp only [CollatzResearch.WordTrace]
  refine ⟨17966634488398181398013657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11977756325598787598675771 17966634488398181398013657)
  ·
    refine ⟨13474975866298636048510243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17966634488398181398013657 13474975866298636048510243)
    ·
      refine ⟨20212463799447954072765365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13474975866298636048510243 20212463799447954072765365)
      ·
        refine ⟨1894918481198245694321753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20212463799447954072765365 1894918481198245694321753)
        ·
          refine ⟨1421188860898684270741315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1894918481198245694321753 1421188860898684270741315)
          ·
            refine ⟨2131783291348026406111973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1421188860898684270741315 2131783291348026406111973)
            ·
              refine ⟨399709367127754951145995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2131783291348026406111973 399709367127754951145995)
              ·
                refine ⟨599564050691632426718993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 399709367127754951145995 599564050691632426718993)
                ·
                  refine ⟨449673038018724320039245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 599564050691632426718993 449673038018724320039245)
                  ·
                    refine ⟨168627389257021620014717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 449673038018724320039245 168627389257021620014717)
                    ·
                      rfl

theorem cell22_492601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 4, 1, 2, 3].length) (baseStart_492601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_492601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_492601 prefixEnd_492601 := by exact prefixLift 492601
  have htrace : WordTrace (prefixWord ++ tailWord_492601) baseStart_492601 baseEnd_492601 := by
    simpa [prefixWord, tailWord_492601, baseEnd_492601] using wordTrace_append hprefix tailTrace_492601
  have hstable : (prefixWord ++ tailWord_492601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492601).length < 2 ^ (prefixWord ++ tailWord_492601).sum := by decide
  have hdescent : baseEnd_492601 < baseStart_492601 := by decide
  rcases family_descends (prefixWord ++ tailWord_492601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492614 : List Nat := [6, 1, 1, 1, 1, 2, 2, 8]
def baseStart_492614 : Nat := 118140960795 + 492614 * 2 ^ 59
def prefixEnd_492614 : Nat := 4983230072969 + 3 ^ 40 * 492614 * 2
def baseEnd_492614 : Nat := 18736871046965991048853

theorem tailTrace_492614 : CollatzResearch.WordTrace tailWord_492614 prefixEnd_492614 18736871046965991048853 := by
  unfold tailWord_492614
  simp only [CollatzResearch.WordTrace]
  refine ⟨561472144917221394319903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11978072424900723078824597 561472144917221394319903)
  ·
    refine ⟨842208217375832091479855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 561472144917221394319903 842208217375832091479855)
    ·
      refine ⟨1263312326063748137219783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 842208217375832091479855 1263312326063748137219783)
      ·
        refine ⟨1894968489095622205829675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1263312326063748137219783 1894968489095622205829675)
        ·
          refine ⟨2842452733643433308744513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1894968489095622205829675 2842452733643433308744513)
          ·
            refine ⟨2131839550232574981558385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2842452733643433308744513 2131839550232574981558385)
            ·
              refine ⟨1598879662674431236168789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2131839550232574981558385 1598879662674431236168789)
              ·
                refine ⟨18736871046965991048853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1598879662674431236168789 18736871046965991048853)
                ·
                  rfl

theorem cell22_492614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_492614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_492614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_492614 prefixEnd_492614 := by exact prefixLift 492614
  have htrace : WordTrace (prefixWord ++ tailWord_492614) baseStart_492614 baseEnd_492614 := by
    simpa [prefixWord, tailWord_492614, baseEnd_492614] using wordTrace_append hprefix tailTrace_492614
  have hstable : (prefixWord ++ tailWord_492614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492614).length < 2 ^ (prefixWord ++ tailWord_492614).sum := by decide
  have hdescent : baseEnd_492614 < baseStart_492614 := by decide
  rcases family_descends (prefixWord ++ tailWord_492614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492625 : List Nat := [1, 2, 2, 1, 3, 1, 2, 1, 9]
def baseStart_492625 : Nat := 118140960795 + 492625 * 2 ^ 59
def prefixEnd_492625 : Nat := 4983230072969 + 3 ^ 40 * 492625 * 2
def baseEnd_492625 : Nat := 56211868315831185804881

theorem tailTrace_492625 : CollatzResearch.WordTrace tailWord_492625 prefixEnd_492625 56211868315831185804881 := by
  unfold tailWord_492625
  simp only [CollatzResearch.WordTrace]
  refine ⟨17967509840311233496887329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11978339893540822331258219 17967509840311233496887329)
  ·
    refine ⟨13475632380233425122665497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17967509840311233496887329 13475632380233425122665497)
    ·
      refine ⟨10106724285175068841999123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13475632380233425122665497 10106724285175068841999123)
      ·
        refine ⟨15160086427762603262998685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10106724285175068841999123 15160086427762603262998685)
        ·
          refine ⟨5685032410410976223624507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15160086427762603262998685 5685032410410976223624507)
          ·
            refine ⟨8527548615616464335436761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5685032410410976223624507 8527548615616464335436761)
            ·
              refine ⟨6395661461712348251577571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8527548615616464335436761 6395661461712348251577571)
              ·
                refine ⟨9593492192568522377366357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6395661461712348251577571 9593492192568522377366357)
                ·
                  refine ⟨56211868315831185804881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 9593492192568522377366357 56211868315831185804881)
                  ·
                    rfl

theorem cell22_492625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 9].length) (baseStart_492625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_492625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_492625 prefixEnd_492625 := by exact prefixLift 492625
  have htrace : WordTrace (prefixWord ++ tailWord_492625) baseStart_492625 baseEnd_492625 := by
    simpa [prefixWord, tailWord_492625, baseEnd_492625] using wordTrace_append hprefix tailTrace_492625
  have hstable : (prefixWord ++ tailWord_492625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492625).length < 2 ^ (prefixWord ++ tailWord_492625).sum := by decide
  have hdescent : baseEnd_492625 < baseStart_492625 := by decide
  rcases family_descends (prefixWord ++ tailWord_492625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492672 : List Nat := [2, 1, 1, 2, 1, 3, 4, 1, 3, 4]
def baseStart_492672 : Nat := 118140960795 + 492672 * 2 ^ 59
def prefixEnd_492672 : Nat := 4983230072969 + 3 ^ 40 * 492672 * 2
def baseEnd_492672 : Nat := 168651694008001101489499

theorem tailTrace_492672 : CollatzResearch.WordTrace tailWord_492672 prefixEnd_492672 168651694008001101489499 := by
  unfold tailWord_492672
  simp only [CollatzResearch.WordTrace]
  refine ⟨8984612035570480261924135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11979482714093973682565513 8984612035570480261924135)
  ·
    refine ⟨13476918053355720392886203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8984612035570480261924135 13476918053355720392886203)
    ·
      refine ⟨20215377080033580589329305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13476918053355720392886203 20215377080033580589329305)
      ·
        refine ⟨15161532810025185441996979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20215377080033580589329305 15161532810025185441996979)
        ·
          refine ⟨22742299215037778162995469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15161532810025185441996979 22742299215037778162995469)
          ·
            refine ⟨8528362205639166811123301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22742299215037778162995469 8528362205639166811123301)
            ·
              refine ⟨1599067913557343777085619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8528362205639166811123301 1599067913557343777085619)
              ·
                refine ⟨2398601870336015665628429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1599067913557343777085619 2398601870336015665628429)
                ·
                  refine ⟨899475701376005874610661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2398601870336015665628429 899475701376005874610661)
                  ·
                    refine ⟨168651694008001101489499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 899475701376005874610661 168651694008001101489499)
                    ·
                      rfl

theorem cell22_492672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 3, 4].length) (baseStart_492672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_492672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_492672 prefixEnd_492672 := by exact prefixLift 492672
  have htrace : WordTrace (prefixWord ++ tailWord_492672) baseStart_492672 baseEnd_492672 := by
    simpa [prefixWord, tailWord_492672, baseEnd_492672] using wordTrace_append hprefix tailTrace_492672
  have hstable : (prefixWord ++ tailWord_492672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492672).length < 2 ^ (prefixWord ++ tailWord_492672).sum := by decide
  have hdescent : baseEnd_492672 < baseStart_492672 := by decide
  rcases family_descends (prefixWord ++ tailWord_492672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492704 : List Nat := [2, 1, 1, 4, 2, 1, 1, 6, 4]
def baseStart_492704 : Nat := 118140960795 + 492704 * 2 ^ 59
def prefixEnd_492704 : Nat := 4983230072969 + 3 ^ 40 * 492704 * 2
def baseEnd_492704 : Nat := 56220882753987894896467

theorem tailTrace_492704 : CollatzResearch.WordTrace tailWord_492704 prefixEnd_492704 56220882753987894896467 := by
  unfold tailWord_492704
  simp only [CollatzResearch.WordTrace]
  refine ⟨8985195603512514994506583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11980260804683353326008777 8985195603512514994506583)
  ·
    refine ⟨13477793405268772491759875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8985195603512514994506583 13477793405268772491759875)
    ·
      refine ⟨20216690107903158737639813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13477793405268772491759875 20216690107903158737639813)
      ·
        refine ⟨3790629395231842263307465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20216690107903158737639813 3790629395231842263307465)
        ·
          refine ⟨2842972046423881697480599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3790629395231842263307465 2842972046423881697480599)
          ·
            refine ⟨4264458069635822546220899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2842972046423881697480599 4264458069635822546220899)
            ·
              refine ⟨6396687104453733819331349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4264458069635822546220899 6396687104453733819331349)
              ·
                refine ⟨299844708021268772781157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6396687104453733819331349 299844708021268772781157)
                ·
                  refine ⟨56220882753987894896467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 299844708021268772781157 56220882753987894896467)
                  ·
                    rfl

theorem cell22_492704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 6, 4].length) (baseStart_492704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_492704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_492704 prefixEnd_492704 := by exact prefixLift 492704
  have htrace : WordTrace (prefixWord ++ tailWord_492704) baseStart_492704 baseEnd_492704 := by
    simpa [prefixWord, tailWord_492704, baseEnd_492704] using wordTrace_append hprefix tailTrace_492704
  have hstable : (prefixWord ++ tailWord_492704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492704).length < 2 ^ (prefixWord ++ tailWord_492704).sum := by decide
  have hdescent : baseEnd_492704 < baseStart_492704 := by decide
  rcases family_descends (prefixWord ++ tailWord_492704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492719 : List Nat := [1, 1, 2, 1, 2, 3, 2, 5, 2, 3]
def baseStart_492719 : Nat := 118140960795 + 492719 * 2 ^ 59
def prefixEnd_492719 : Nat := 4983230072969 + 3 ^ 40 * 492719 * 2
def baseEnd_492719 : Nat := 168667783068508645564355

theorem tailTrace_492719 : CollatzResearch.WordTrace tailWord_492719 prefixEnd_492719 168667783068508645564355 := by
  unfold tailWord_492719
  simp only [CollatzResearch.WordTrace]
  refine ⟨17970938301970687550809211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11980625534647125033872807 17970938301970687550809211)
  ·
    refine ⟨26956407452956031326213817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17970938301970687550809211 26956407452956031326213817)
    ·
      refine ⟨20217305589717023494660363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26956407452956031326213817 20217305589717023494660363)
      ·
        refine ⟨30325958384575535241990545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20217305589717023494660363 30325958384575535241990545)
        ·
          refine ⟨22744468788431651431492909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30325958384575535241990545 22744468788431651431492909)
          ·
            refine ⟨8529175795661869286809841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22744468788431651431492909 8529175795661869286809841)
            ·
              refine ⟨6396881846746401965107381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8529175795661869286809841 6396881846746401965107381)
              ·
                refine ⟨599707673132475184228817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6396881846746401965107381 599707673132475184228817)
                ·
                  refine ⟨449780754849356388171613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 599707673132475184228817 449780754849356388171613)
                  ·
                    refine ⟨168667783068508645564355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 449780754849356388171613 168667783068508645564355)
                    ·
                      rfl

theorem cell22_492719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 5, 2, 3].length) (baseStart_492719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_492719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_492719 prefixEnd_492719 := by exact prefixLift 492719
  have htrace : WordTrace (prefixWord ++ tailWord_492719) baseStart_492719 baseEnd_492719 := by
    simpa [prefixWord, tailWord_492719, baseEnd_492719] using wordTrace_append hprefix tailTrace_492719
  have hstable : (prefixWord ++ tailWord_492719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492719).length < 2 ^ (prefixWord ++ tailWord_492719).sum := by decide
  have hdescent : baseEnd_492719 < baseStart_492719 := by decide
  rcases family_descends (prefixWord ++ tailWord_492719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492734 : List Nat := [4, 2, 1, 1, 3, 1, 2, 1, 1, 6]
def baseStart_492734 : Nat := 118140960795 + 492734 * 2 ^ 59
def prefixEnd_492734 : Nat := 4983230072969 + 3 ^ 40 * 492734 * 2
def baseEnd_492734 : Nat := 168672917875053606439309

theorem tailTrace_492734 : CollatzResearch.WordTrace tailWord_492734 prefixEnd_492734 168672917875053606439309 := by
  unfold tailWord_492734
  simp only [CollatzResearch.WordTrace]
  refine ⟨2246435674614543139075657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11980990264610896741736837 2246435674614543139075657)
  ·
    refine ⟨1684826755960907354306743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2246435674614543139075657 1684826755960907354306743)
    ·
      refine ⟨2527240133941361031460115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1684826755960907354306743 2527240133941361031460115)
      ·
        refine ⟨3790860200912041547190173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2527240133941361031460115 3790860200912041547190173)
        ·
          refine ⟨1421572575342015580196315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3790860200912041547190173 1421572575342015580196315)
          ·
            refine ⟨2132358863013023370294473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1421572575342015580196315 2132358863013023370294473)
            ·
              refine ⟨1599269147259767527720855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2132358863013023370294473 1599269147259767527720855)
              ·
                refine ⟨2398903720889651291581283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1599269147259767527720855 2398903720889651291581283)
                ·
                  refine ⟨3598355581334476937371925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2398903720889651291581283 3598355581334476937371925)
                  ·
                    refine ⟨168672917875053606439309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3598355581334476937371925 168672917875053606439309)
                    ·
                      rfl

theorem cell22_492734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_492734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_492734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_492734 prefixEnd_492734 := by exact prefixLift 492734
  have htrace : WordTrace (prefixWord ++ tailWord_492734) baseStart_492734 baseEnd_492734 := by
    simpa [prefixWord, tailWord_492734, baseEnd_492734] using wordTrace_append hprefix tailTrace_492734
  have hstable : (prefixWord ++ tailWord_492734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492734).length < 2 ^ (prefixWord ++ tailWord_492734).sum := by decide
  have hdescent : baseEnd_492734 < baseStart_492734 := by decide
  rcases family_descends (prefixWord ++ tailWord_492734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492762 : List Nat := [3, 1, 1, 2, 2, 1, 1, 3, 2, 6]
def baseStart_492762 : Nat := 118140960795 + 492762 * 2 ^ 59
def prefixEnd_492762 : Nat := 4983230072969 + 3 ^ 40 * 492762 * 2
def baseEnd_492762 : Nat := 168682502847270866739223

theorem tailTrace_492762 : CollatzResearch.WordTrace tailWord_492762 prefixEnd_492762 168682502847270866739223 := by
  unfold tailWord_492762
  simp only [CollatzResearch.WordTrace]
  refine ⟨4493126660203726473656135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11981671093876603929749693 4493126660203726473656135)
  ·
    refine ⟨6739689990305589710484203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4493126660203726473656135 6739689990305589710484203)
    ·
      refine ⟨10109534985458384565726305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6739689990305589710484203 10109534985458384565726305)
      ·
        refine ⟨7582151239093788424294729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10109534985458384565726305 7582151239093788424294729)
        ·
          refine ⟨5686613429320341318221047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7582151239093788424294729 5686613429320341318221047)
          ·
            refine ⟨8529920143980511977331571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5686613429320341318221047 8529920143980511977331571)
            ·
              refine ⟨12794880215970767965997357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8529920143980511977331571 12794880215970767965997357)
              ·
                refine ⟨4798080080989037987249009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12794880215970767965997357 4798080080989037987249009)
                ·
                  refine ⟨3598560060741778490436757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4798080080989037987249009 3598560060741778490436757)
                  ·
                    refine ⟨168682502847270866739223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3598560060741778490436757 168682502847270866739223)
                    ·
                      rfl

theorem cell22_492762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 2, 6].length) (baseStart_492762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_492762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_492762 prefixEnd_492762 := by exact prefixLift 492762
  have htrace : WordTrace (prefixWord ++ tailWord_492762) baseStart_492762 baseEnd_492762 := by
    simpa [prefixWord, tailWord_492762, baseEnd_492762] using wordTrace_append hprefix tailTrace_492762
  have hstable : (prefixWord ++ tailWord_492762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492762).length < 2 ^ (prefixWord ++ tailWord_492762).sum := by decide
  have hdescent : baseEnd_492762 < baseStart_492762 := by decide
  rcases family_descends (prefixWord ++ tailWord_492762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492792 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 6, 5]
def baseStart_492792 : Nat := 118140960795 + 492792 * 2 ^ 59
def prefixEnd_492792 : Nat := 4983230072969 + 3 ^ 40 * 492792 * 2
def baseEnd_492792 : Nat := 168692772460360788489131

theorem tailTrace_492792 : CollatzResearch.WordTrace tailWord_492792 prefixEnd_492792 168692772460360788489131 := by
  unfold tailWord_492792
  simp only [CollatzResearch.WordTrace]
  refine ⟨8986800415353110509108315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11982400553804147345477753 8986800415353110509108315)
  ·
    refine ⟨13480200623029665763662473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8986800415353110509108315 13480200623029665763662473)
    ·
      refine ⟨10110150467272249322746855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13480200623029665763662473 10110150467272249322746855)
      ·
        refine ⟨15165225700908373984120283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10110150467272249322746855 15165225700908373984120283)
        ·
          refine ⟨22747838551362560976180425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15165225700908373984120283 22747838551362560976180425)
          ·
            refine ⟨17060878913521920732135319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22747838551362560976180425 17060878913521920732135319)
            ·
              refine ⟨25591318370282881098202979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17060878913521920732135319 25591318370282881098202979)
              ·
                refine ⟨38386977555424321647304469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25591318370282881098202979 38386977555424321647304469)
                ·
                  refine ⟨1799389572910515077217397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 38386977555424321647304469 1799389572910515077217397)
                  ·
                    refine ⟨168692772460360788489131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1799389572910515077217397 168692772460360788489131)
                    ·
                      rfl

theorem cell22_492792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 6, 5].length) (baseStart_492792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_492792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_492792 prefixEnd_492792 := by exact prefixLift 492792
  have htrace : WordTrace (prefixWord ++ tailWord_492792) baseStart_492792 baseEnd_492792 := by
    simpa [prefixWord, tailWord_492792, baseEnd_492792] using wordTrace_append hprefix tailTrace_492792
  have hstable : (prefixWord ++ tailWord_492792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492792).length < 2 ^ (prefixWord ++ tailWord_492792).sum := by decide
  have hdescent : baseEnd_492792 < baseStart_492792 := by decide
  rcases family_descends (prefixWord ++ tailWord_492792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492824 : List Nat := [2, 1, 2, 3, 1, 3, 1, 2, 3, 4]
def baseStart_492824 : Nat := 118140960795 + 492824 * 2 ^ 59
def prefixEnd_492824 : Nat := 4983230072969 + 3 ^ 40 * 492824 * 2
def baseEnd_492824 : Nat := 168703726714323371689033

theorem tailTrace_492824 : CollatzResearch.WordTrace tailWord_492824 prefixEnd_492824 168703726714323371689033 := by
  unfold tailWord_492824
  simp only [CollatzResearch.WordTrace]
  refine ⟨8987383983295145241690763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11983178644393526988921017 8987383983295145241690763)
  ·
    refine ⟨13481075974942717862536145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8987383983295145241690763 13481075974942717862536145)
    ·
      refine ⟨10110806981207038396902109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13481075974942717862536145 10110806981207038396902109)
      ·
        refine ⟨3791552617952639398838291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10110806981207038396902109 3791552617952639398838291)
        ·
          refine ⟨5687328926928959098257437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3791552617952639398838291 5687328926928959098257437)
          ·
            refine ⟨2132748347598359661846539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5687328926928959098257437 2132748347598359661846539)
            ·
              refine ⟨3199122521397539492769809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2132748347598359661846539 3199122521397539492769809)
              ·
                refine ⟨2399341891048154619577357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3199122521397539492769809 2399341891048154619577357)
                ·
                  refine ⟨899753209143057982341509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2399341891048154619577357 899753209143057982341509)
                  ·
                    refine ⟨168703726714323371689033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 899753209143057982341509 168703726714323371689033)
                    ·
                      rfl

theorem cell22_492824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 3, 4].length) (baseStart_492824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_492824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_492824 prefixEnd_492824 := by exact prefixLift 492824
  have htrace : WordTrace (prefixWord ++ tailWord_492824) baseStart_492824 baseEnd_492824 := by
    simpa [prefixWord, tailWord_492824, baseEnd_492824] using wordTrace_append hprefix tailTrace_492824
  have hstable : (prefixWord ++ tailWord_492824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492824).length < 2 ^ (prefixWord ++ tailWord_492824).sum := by decide
  have hdescent : baseEnd_492824 < baseStart_492824 := by decide
  rcases family_descends (prefixWord ++ tailWord_492824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492869 : List Nat := [1, 3, 1, 1, 1, 2, 1, 6, 2, 4]
def baseStart_492869 : Nat := 118140960795 + 492869 * 2 ^ 59
def prefixEnd_492869 : Nat := 4983230072969 + 3 ^ 40 * 492869 * 2
def baseEnd_492869 : Nat := 168719131133958254313895

theorem tailTrace_492869 : CollatzResearch.WordTrace tailWord_492869 prefixEnd_492869 168719131133958254313895 := by
  unfold tailWord_492869
  simp only [CollatzResearch.WordTrace]
  refine ⟨17976409251427263168769661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11984272834284842112513107 17976409251427263168769661)
  ·
    refine ⟨6741153469285223688288623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17976409251427263168769661 6741153469285223688288623)
    ·
      refine ⟨10111730203927835532432935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6741153469285223688288623 10111730203927835532432935)
      ·
        refine ⟨15167595305891753298649403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10111730203927835532432935 15167595305891753298649403)
        ·
          refine ⟨22751392958837629947974105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15167595305891753298649403 22751392958837629947974105)
          ·
            refine ⟨17063544719128222460980579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22751392958837629947974105 17063544719128222460980579)
            ·
              refine ⟨25595317078692333691470869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17063544719128222460980579 25595317078692333691470869)
              ·
                refine ⟨1199780488063703141787697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25595317078692333691470869 1199780488063703141787697)
                ·
                  refine ⟨899835366047777356340773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1199780488063703141787697 899835366047777356340773)
                  ·
                    refine ⟨168719131133958254313895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 899835366047777356340773 168719131133958254313895)
                    ·
                      rfl

theorem cell22_492869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 6, 2, 4].length) (baseStart_492869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_492869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_492869 prefixEnd_492869 := by exact prefixLift 492869
  have htrace : WordTrace (prefixWord ++ tailWord_492869) baseStart_492869 baseEnd_492869 := by
    simpa [prefixWord, tailWord_492869, baseEnd_492869] using wordTrace_append hprefix tailTrace_492869
  have hstable : (prefixWord ++ tailWord_492869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492869).length < 2 ^ (prefixWord ++ tailWord_492869).sum := by decide
  have hdescent : baseEnd_492869 < baseStart_492869 := by decide
  rcases family_descends (prefixWord ++ tailWord_492869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492871 : List Nat := [1, 1, 4, 1, 2, 4, 1, 1, 4, 3]
def baseStart_492871 : Nat := 118140960795 + 492871 * 2 ^ 59
def prefixEnd_492871 : Nat := 4983230072969 + 3 ^ 40 * 492871 * 2
def baseEnd_492871 : Nat := 168719815774830915763889

theorem tailTrace_492871 : CollatzResearch.WordTrace tailWord_492871 prefixEnd_492871 168719815774830915763889 := by
  unfold tailWord_492871
  simp only [CollatzResearch.WordTrace]
  refine ⟨17976482197420017510342467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11984321464946678340228311 17976482197420017510342467)
  ·
    refine ⟨26964723296130026265513701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17976482197420017510342467 26964723296130026265513701)
    ·
      refine ⟨5055885618024379924783819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26964723296130026265513701 5055885618024379924783819)
      ·
        refine ⟨7583828427036569887175729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5055885618024379924783819 7583828427036569887175729)
        ·
          refine ⟨5687871320277427415381797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7583828427036569887175729 5687871320277427415381797)
          ·
            refine ⟨1066475872552017640384087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5687871320277427415381797 1066475872552017640384087)
            ·
              refine ⟨1599713808828026460576131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1066475872552017640384087 1599713808828026460576131)
              ·
                refine ⟨2399570713242039690864197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1599713808828026460576131 2399570713242039690864197)
                ·
                  refine ⟨449919508732882442037037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2399570713242039690864197 449919508732882442037037)
                  ·
                    refine ⟨168719815774830915763889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 449919508732882442037037 168719815774830915763889)
                    ·
                      rfl

theorem cell22_492871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 4, 3].length) (baseStart_492871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_492871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_492871 prefixEnd_492871 := by exact prefixLift 492871
  have htrace : WordTrace (prefixWord ++ tailWord_492871) baseStart_492871 baseEnd_492871 := by
    simpa [prefixWord, tailWord_492871, baseEnd_492871] using wordTrace_append hprefix tailTrace_492871
  have hstable : (prefixWord ++ tailWord_492871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492871).length < 2 ^ (prefixWord ++ tailWord_492871).sum := by decide
  have hdescent : baseEnd_492871 < baseStart_492871 := by decide
  rcases family_descends (prefixWord ++ tailWord_492871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492884 : List Nat := [2, 4, 1, 1, 2, 1, 2, 9]
def baseStart_492884 : Nat := 118140960795 + 492884 * 2 ^ 59
def prefixEnd_492884 : Nat := 4983230072969 + 3 ^ 40 * 492884 * 2
def baseEnd_492884 : Nat := 18747140660055912798761

theorem tailTrace_492884 : CollatzResearch.WordTrace tailWord_492884 prefixEnd_492884 18747140660055912798761 := by
  unfold tailWord_492884
  simp only [CollatzResearch.WordTrace]
  refine ⟨8988478173186460365282853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11984637564248613820377137 8988478173186460365282853)
  ·
    refine ⟨1685339657472461318490535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8988478173186460365282853 1685339657472461318490535)
    ·
      refine ⟨2528009486208691977735803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1685339657472461318490535 2528009486208691977735803)
      ·
        refine ⟨3792014229313037966603705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2528009486208691977735803 3792014229313037966603705)
        ·
          refine ⟨2844010671984778474952779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3792014229313037966603705 2844010671984778474952779)
          ·
            refine ⟨4266016007977167712429169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2844010671984778474952779 4266016007977167712429169)
            ·
              refine ⟨3199512005982875784321877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4266016007977167712429169 3199512005982875784321877)
              ·
                refine ⟨18747140660055912798761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3199512005982875784321877 18747140660055912798761)
                ·
                  rfl

theorem cell22_492884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 9].length) (baseStart_492884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_492884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_492884 prefixEnd_492884 := by exact prefixLift 492884
  have htrace : WordTrace (prefixWord ++ tailWord_492884) baseStart_492884 baseEnd_492884 := by
    simpa [prefixWord, tailWord_492884, baseEnd_492884] using wordTrace_append hprefix tailTrace_492884
  have hstable : (prefixWord ++ tailWord_492884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492884).length < 2 ^ (prefixWord ++ tailWord_492884).sum := by decide
  have hdescent : baseEnd_492884 < baseStart_492884 := by decide
  rcases family_descends (prefixWord ++ tailWord_492884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492888 : List Nat := [2, 1, 2, 2, 1, 1, 7, 1, 2, 3]
def baseStart_492888 : Nat := 118140960795 + 492888 * 2 ^ 59
def prefixEnd_492888 : Nat := 4983230072969 + 3 ^ 40 * 492888 * 2
def baseEnd_492888 : Nat := 168725635222248538088837

theorem tailTrace_492888 : CollatzResearch.WordTrace tailWord_492888 prefixEnd_492888 168725635222248538088837 := by
  unfold tailWord_492888
  simp only [CollatzResearch.WordTrace]
  refine ⟨8988551119179214706855659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11984734825572286275807545 8988551119179214706855659)
  ·
    refine ⟨13482826678768822060283489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8988551119179214706855659 13482826678768822060283489)
    ·
      refine ⟨10112120009076616545212617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13482826678768822060283489 10112120009076616545212617)
      ·
        refine ⟨7584090006807462408909463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10112120009076616545212617 7584090006807462408909463)
        ·
          refine ⟨11376135010211193613364195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7584090006807462408909463 11376135010211193613364195)
          ·
            refine ⟨17064202515316790420046293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11376135010211193613364195 17064202515316790420046293)
            ·
              refine ⟨399942246452737275469835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 17064202515316790420046293 399942246452737275469835)
              ·
                refine ⟨599913369679105913204753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 399942246452737275469835 599913369679105913204753)
                ·
                  refine ⟨449935027259329434903565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 599913369679105913204753 449935027259329434903565)
                  ·
                    refine ⟨168725635222248538088837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 449935027259329434903565 168725635222248538088837)
                    ·
                      rfl

theorem cell22_492888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7, 1, 2, 3].length) (baseStart_492888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_492888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_492888 prefixEnd_492888 := by exact prefixLift 492888
  have htrace : WordTrace (prefixWord ++ tailWord_492888) baseStart_492888 baseEnd_492888 := by
    simpa [prefixWord, tailWord_492888, baseEnd_492888] using wordTrace_append hprefix tailTrace_492888
  have hstable : (prefixWord ++ tailWord_492888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492888).length < 2 ^ (prefixWord ++ tailWord_492888).sum := by decide
  have hdescent : baseEnd_492888 < baseStart_492888 := by decide
  rcases family_descends (prefixWord ++ tailWord_492888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492933 : List Nat := [1, 3, 1, 1, 3, 1, 2, 6, 1, 3]
def baseStart_492933 : Nat := 118140960795 + 492933 * 2 ^ 59
def prefixEnd_492933 : Nat := 4983230072969 + 3 ^ 40 * 492933 * 2
def baseEnd_492933 : Nat := 168741039641883420713699

theorem tailTrace_492933 : CollatzResearch.WordTrace tailWord_492933 prefixEnd_492933 168741039641883420713699 := by
  unfold tailWord_492933
  simp only [CollatzResearch.WordTrace]
  refine ⟨17978743523195402099099453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11985829015463601399399635 17978743523195402099099453)
  ·
    refine ⟨6742028821198275787162295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17978743523195402099099453 6742028821198275787162295)
    ·
      refine ⟨10113043231797413680743443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6742028821198275787162295 10113043231797413680743443)
      ·
        refine ⟨15169564847696120521115165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10113043231797413680743443 15169564847696120521115165)
        ·
          refine ⟨5688586817886045195418187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15169564847696120521115165 5688586817886045195418187)
          ·
            refine ⟨8532880226829067793127281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5688586817886045195418187 8532880226829067793127281)
            ·
              refine ⟨6399660170121800844845461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8532880226829067793127281 6399660170121800844845461)
              ·
                refine ⟨299984070474459414602131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6399660170121800844845461 299984070474459414602131)
                ·
                  refine ⟨449976105711689121903197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 299984070474459414602131 449976105711689121903197)
                  ·
                    refine ⟨168741039641883420713699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 449976105711689121903197 168741039641883420713699)
                    ·
                      rfl

theorem cell22_492933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 6, 1, 3].length) (baseStart_492933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_492933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_492933 prefixEnd_492933 := by exact prefixLift 492933
  have htrace : WordTrace (prefixWord ++ tailWord_492933) baseStart_492933 baseEnd_492933 := by
    simpa [prefixWord, tailWord_492933, baseEnd_492933] using wordTrace_append hprefix tailTrace_492933
  have hstable : (prefixWord ++ tailWord_492933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492933).length < 2 ^ (prefixWord ++ tailWord_492933).sum := by decide
  have hdescent : baseEnd_492933 < baseStart_492933 := by decide
  rcases family_descends (prefixWord ++ tailWord_492933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493006 : List Nat := [4, 1, 1, 1, 2, 1, 3, 3, 1, 5]
def baseStart_493006 : Nat := 118140960795 + 493006 * 2 ^ 59
def prefixEnd_493006 : Nat := 4983230072969 + 3 ^ 40 * 493006 * 2
def baseEnd_493006 : Nat := 168766029033735563638475

theorem tailTrace_493006 : CollatzResearch.WordTrace tailWord_493006 prefixEnd_493006 168766029033735563638475 := by
  unfold tailWord_493006
  simp only [CollatzResearch.WordTrace]
  refine ⟨2247675756491366945813359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11987604034620623711004581 2247675756491366945813359)
  ·
    refine ⟨3371513634737050418720039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2247675756491366945813359 3371513634737050418720039)
    ·
      refine ⟨5057270452105575628080059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3371513634737050418720039 5057270452105575628080059)
      ·
        refine ⟨7585905678158363442120089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5057270452105575628080059 7585905678158363442120089)
        ·
          refine ⟨5689429258618772581590067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7585905678158363442120089 5689429258618772581590067)
          ·
            refine ⟨8534143887928158872385101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5689429258618772581590067 8534143887928158872385101)
            ·
              refine ⟨3200303957973059577144413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8534143887928158872385101 3200303957973059577144413)
              ·
                refine ⟨1200113984239897341429155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3200303957973059577144413 1200113984239897341429155)
                ·
                  refine ⟨1800170976359846012143733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1200113984239897341429155 1800170976359846012143733)
                  ·
                    refine ⟨168766029033735563638475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1800170976359846012143733 168766029033735563638475)
                    ·
                      rfl

theorem cell22_493006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_493006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_493006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_493006 prefixEnd_493006 := by exact prefixLift 493006
  have htrace : WordTrace (prefixWord ++ tailWord_493006) baseStart_493006 baseEnd_493006 := by
    simpa [prefixWord, tailWord_493006, baseEnd_493006] using wordTrace_append hprefix tailTrace_493006
  have hstable : (prefixWord ++ tailWord_493006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493006).length < 2 ^ (prefixWord ++ tailWord_493006).sum := by decide
  have hdescent : baseEnd_493006 < baseStart_493006 := by decide
  rcases family_descends (prefixWord ++ tailWord_493006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493040 : List Nat := [2, 1, 1, 1, 3, 6, 1, 2, 2, 3]
def baseStart_493040 : Nat := 118140960795 + 493040 * 2 ^ 59
def prefixEnd_493040 : Nat := 4983230072969 + 3 ^ 40 * 493040 * 2
def baseEnd_493040 : Nat := 168777667928570808288371

theorem tailTrace_493040 : CollatzResearch.WordTrace tailWord_493040 prefixEnd_493040 168777667928570808288371 := by
  unfold tailWord_493040
  simp only [CollatzResearch.WordTrace]
  refine ⟨8991323066903879686622287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11988430755871839582163049 8991323066903879686622287)
  ·
    refine ⟨13486984600355819529933431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8991323066903879686622287 13486984600355819529933431)
    ·
      refine ⟨20230476900533729294900147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13486984600355819529933431 20230476900533729294900147)
      ·
        refine ⟨30345715350800593942350221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20230476900533729294900147 30345715350800593942350221)
        ·
          refine ⟨11379643256550222728381333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30345715350800593942350221 11379643256550222728381333)
          ·
            refine ⟨533420777650791690392875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 11379643256550222728381333 533420777650791690392875)
            ·
              refine ⟨800131166476187535589313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 533420777650791690392875 800131166476187535589313)
              ·
                refine ⟨600098374857140651691985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 800131166476187535589313 600098374857140651691985)
                ·
                  refine ⟨450073781142855488768989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 600098374857140651691985 450073781142855488768989)
                  ·
                    refine ⟨168777667928570808288371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 450073781142855488768989 168777667928570808288371)
                    ·
                      rfl

theorem cell22_493040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 2, 2, 3].length) (baseStart_493040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_493040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_493040 prefixEnd_493040 := by exact prefixLift 493040
  have htrace : WordTrace (prefixWord ++ tailWord_493040) baseStart_493040 baseEnd_493040 := by
    simpa [prefixWord, tailWord_493040, baseEnd_493040] using wordTrace_append hprefix tailTrace_493040
  have hstable : (prefixWord ++ tailWord_493040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493040).length < 2 ^ (prefixWord ++ tailWord_493040).sum := by decide
  have hdescent : baseEnd_493040 < baseStart_493040 := by decide
  rcases family_descends (prefixWord ++ tailWord_493040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493051 : List Nat := [1, 1, 1, 1, 1, 3, 2, 2, 7, 3]
def baseStart_493051 : Nat := 118140960795 + 493051 * 2 ^ 59
def prefixEnd_493051 : Nat := 4983230072969 + 3 ^ 40 * 493051 * 2
def baseEnd_493051 : Nat := 168781433453370446263337

theorem tailTrace_493051 : CollatzResearch.WordTrace tailWord_493051 prefixEnd_493051 168781433453370446263337 := by
  unfold tailWord_493051
  simp only [CollatzResearch.WordTrace]
  refine ⟨17983047336767908251895007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11988698224511938834596671 17983047336767908251895007)
  ·
    refine ⟨26974571005151862377842511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17983047336767908251895007 26974571005151862377842511)
    ·
      refine ⟨40461856507727793566763767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26974571005151862377842511 40461856507727793566763767)
      ·
        refine ⟨60692784761591690350145651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40461856507727793566763767 60692784761591690350145651)
        ·
          refine ⟨91039177142387535525218477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60692784761591690350145651 91039177142387535525218477)
          ·
            refine ⟨34139691428395325821956929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91039177142387535525218477 34139691428395325821956929)
            ·
              refine ⟨25604768571296494366467697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34139691428395325821956929 25604768571296494366467697)
              ·
                refine ⟨19203576428472370774850773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25604768571296494366467697 19203576428472370774850773)
                ·
                  refine ⟨450083822542321190035565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19203576428472370774850773 450083822542321190035565)
                  ·
                    refine ⟨168781433453370446263337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 450083822542321190035565 168781433453370446263337)
                    ·
                      rfl

theorem cell22_493051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 7, 3].length) (baseStart_493051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_493051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_493051 prefixEnd_493051 := by exact prefixLift 493051
  have htrace : WordTrace (prefixWord ++ tailWord_493051) baseStart_493051 baseEnd_493051 := by
    simpa [prefixWord, tailWord_493051, baseEnd_493051] using wordTrace_append hprefix tailTrace_493051
  have hstable : (prefixWord ++ tailWord_493051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493051).length < 2 ^ (prefixWord ++ tailWord_493051).sum := by decide
  have hdescent : baseEnd_493051 < baseStart_493051 := by decide
  rcases family_descends (prefixWord ++ tailWord_493051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493057 : List Nat := [1, 2, 4, 1, 4, 1, 3, 1, 2, 3]
def baseStart_493057 : Nat := 118140960795 + 493057 * 2 ^ 59
def prefixEnd_493057 : Nat := 4983230072969 + 3 ^ 40 * 493057 * 2
def baseEnd_493057 : Nat := 168783487375988430613319

theorem tailTrace_493057 : CollatzResearch.WordTrace tailWord_493057 prefixEnd_493057 168783487375988430613319 := by
  unfold tailWord_493057
  simp only [CollatzResearch.WordTrace]
  refine ⟨17983266174746171276613425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11988844116497447517742283 17983266174746171276613425)
  ·
    refine ⟨13487449631059628457460069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17983266174746171276613425 13487449631059628457460069)
    ·
      refine ⟨2528896805823680335773763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13487449631059628457460069 2528896805823680335773763)
      ·
        refine ⟨3793345208735520503660645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2528896805823680335773763 3793345208735520503660645)
        ·
          refine ⟨711252226637910094436371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3793345208735520503660645 711252226637910094436371)
          ·
            refine ⟨1066878339956865141654557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 711252226637910094436371 1066878339956865141654557)
            ·
              refine ⟨400079377483824428120459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1066878339956865141654557 400079377483824428120459)
              ·
                refine ⟨600119066225736642180689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 400079377483824428120459 600119066225736642180689)
                ·
                  refine ⟨450089299669302481635517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 600119066225736642180689 450089299669302481635517)
                  ·
                    refine ⟨168783487375988430613319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 450089299669302481635517 168783487375988430613319)
                    ·
                      rfl

theorem cell22_493057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 3, 1, 2, 3].length) (baseStart_493057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_493057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_493057 prefixEnd_493057 := by exact prefixLift 493057
  have htrace : WordTrace (prefixWord ++ tailWord_493057) baseStart_493057 baseEnd_493057 := by
    simpa [prefixWord, tailWord_493057, baseEnd_493057] using wordTrace_append hprefix tailTrace_493057
  have hstable : (prefixWord ++ tailWord_493057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493057).length < 2 ^ (prefixWord ++ tailWord_493057).sum := by decide
  have hdescent : baseEnd_493057 < baseStart_493057 := by decide
  rcases family_descends (prefixWord ++ tailWord_493057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493070 : List Nat := [4, 1, 1, 2, 4, 2, 2, 6]
def baseStart_493070 : Nat := 118140960795 + 493070 * 2 ^ 59
def prefixEnd_493070 : Nat := 4983230072969 + 3 ^ 40 * 493070 * 2
def baseEnd_493070 : Nat := 18754215282406747782031

theorem tailTrace_493070 : CollatzResearch.WordTrace tailWord_493070 prefixEnd_493070 18754215282406747782031 := by
  unfold tailWord_493070
  simp only [CollatzResearch.WordTrace]
  refine ⟨2247967540462384312104583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11989160215799382997891109 2247967540462384312104583)
  ·
    refine ⟨3371951310693576468156875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2247967540462384312104583 3371951310693576468156875)
    ·
      refine ⟨5057926966040364702235313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3371951310693576468156875 5057926966040364702235313)
      ·
        refine ⟨3793445224530273526676485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5057926966040364702235313 3793445224530273526676485)
        ·
          refine ⟨711270979599426286251841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3793445224530273526676485 711270979599426286251841)
          ·
            refine ⟨533453234699569714688881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 711270979599426286251841 533453234699569714688881)
            ·
              refine ⟨400089926024677286016661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 533453234699569714688881 400089926024677286016661)
              ·
                refine ⟨18754215282406747782031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 400089926024677286016661 18754215282406747782031)
                ·
                  rfl

theorem cell22_493070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 2, 6].length) (baseStart_493070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_493070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_493070 prefixEnd_493070 := by exact prefixLift 493070
  have htrace : WordTrace (prefixWord ++ tailWord_493070) baseStart_493070 baseEnd_493070 := by
    simpa [prefixWord, tailWord_493070, baseEnd_493070] using wordTrace_append hprefix tailTrace_493070
  have hstable : (prefixWord ++ tailWord_493070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493070).length < 2 ^ (prefixWord ++ tailWord_493070).sum := by decide
  have hdescent : baseEnd_493070 < baseStart_493070 := by decide
  rcases family_descends (prefixWord ++ tailWord_493070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493098 : List Nat := [3, 1, 4, 1, 1, 1, 2, 4, 5]
def baseStart_493098 : Nat := 118140960795 + 493098 * 2 ^ 59
def prefixEnd_493098 : Nat := 4983230072969 + 3 ^ 40 * 493098 * 2
def baseEnd_493098 : Nat := 56265840837959330112731

theorem tailTrace_493098 : CollatzResearch.WordTrace tailWord_493098 prefixEnd_493098 56265840837959330112731 := by
  unfold tailWord_493098
  simp only [CollatzResearch.WordTrace]
  refine ⟨4496190391899408819713987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11989841045065090185903965 4496190391899408819713987)
  ·
    refine ⟨6744285587849113229570981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4496190391899408819713987 6744285587849113229570981)
    ·
      refine ⟨1264553547721708730544559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6744285587849113229570981 1264553547721708730544559)
      ·
        refine ⟨1896830321582563095816839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1264553547721708730544559 1896830321582563095816839)
        ·
          refine ⟨2845245482373844643725259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1896830321582563095816839 2845245482373844643725259)
          ·
            refine ⟨4267868223560766965587889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2845245482373844643725259 4267868223560766965587889)
            ·
              refine ⟨3200901167670575224190917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4267868223560766965587889 3200901167670575224190917)
              ·
                refine ⟨600168968938232854535797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3200901167670575224190917 600168968938232854535797)
                ·
                  refine ⟨56265840837959330112731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 600168968938232854535797 56265840837959330112731)
                  ·
                    rfl

theorem cell22_493098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 4, 5].length) (baseStart_493098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_493098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_493098 prefixEnd_493098 := by exact prefixLift 493098
  have htrace : WordTrace (prefixWord ++ tailWord_493098) baseStart_493098 baseEnd_493098 := by
    simpa [prefixWord, tailWord_493098, baseEnd_493098] using wordTrace_append hprefix tailTrace_493098
  have hstable : (prefixWord ++ tailWord_493098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493098).length < 2 ^ (prefixWord ++ tailWord_493098).sum := by decide
  have hdescent : baseEnd_493098 < baseStart_493098 := by decide
  rcases family_descends (prefixWord ++ tailWord_493098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493102 : List Nat := [4, 1, 3, 1, 2, 3, 1, 1, 3, 3]
def baseStart_493102 : Nat := 118140960795 + 493102 * 2 ^ 59
def prefixEnd_493102 : Nat := 4983230072969 + 3 ^ 40 * 493102 * 2
def baseEnd_493102 : Nat := 168798891795623313238181

theorem tailTrace_493102 : CollatzResearch.WordTrace tailWord_493102 prefixEnd_493102 168798891795623313238181 := by
  unfold tailWord_493102
  simp only [CollatzResearch.WordTrace]
  refine ⟨2248113432447892995250195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11989938306388762641334373 2248113432447892995250195)
  ·
    refine ⟨3372170148671839492875293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2248113432447892995250195 3372170148671839492875293)
    ·
      refine ⟨1264563805751939809828235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3372170148671839492875293 1264563805751939809828235)
      ·
        refine ⟨1896845708627909714742353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1264563805751939809828235 1896845708627909714742353)
        ·
          refine ⟨1422634281470932286056765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1896845708627909714742353 1422634281470932286056765)
          ·
            refine ⟨533487855551599607271287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1422634281470932286056765 533487855551599607271287)
            ·
              refine ⟨800231783327399410906931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 533487855551599607271287 800231783327399410906931)
              ·
                refine ⟨1200347674991099116360397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 800231783327399410906931 1200347674991099116360397)
                ·
                  refine ⟨450130378121662168635149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1200347674991099116360397 450130378121662168635149)
                  ·
                    refine ⟨168798891795623313238181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 450130378121662168635149 168798891795623313238181)
                    ·
                      rfl

theorem cell22_493102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_493102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_493102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_493102 prefixEnd_493102 := by exact prefixLift 493102
  have htrace : WordTrace (prefixWord ++ tailWord_493102) baseStart_493102 baseEnd_493102 := by
    simpa [prefixWord, tailWord_493102, baseEnd_493102] using wordTrace_append hprefix tailTrace_493102
  have hstable : (prefixWord ++ tailWord_493102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493102).length < 2 ^ (prefixWord ++ tailWord_493102).sum := by decide
  have hdescent : baseEnd_493102 < baseStart_493102 := by decide
  rcases family_descends (prefixWord ++ tailWord_493102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493201 : List Nat := [1, 2, 2, 1, 1, 1, 1, 4, 1, 8]
def baseStart_493201 : Nat := 118140960795 + 493201 * 2 ^ 59
def prefixEnd_493201 : Nat := 4983230072969 + 3 ^ 40 * 493201 * 2
def baseEnd_493201 : Nat := 168832781518820055012877

theorem tailTrace_493201 : CollatzResearch.WordTrace tailWord_493201 prefixEnd_493201 168832781518820055012877 := by
  unfold tailWord_493201
  simp only [CollatzResearch.WordTrace]
  refine ⟨17988518286224483869855457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11992345524149655913236971 17988518286224483869855457)
  ·
    refine ⟨13491388714668362902391593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17988518286224483869855457 13491388714668362902391593)
    ·
      refine ⟨10118541536001272176793695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13491388714668362902391593 10118541536001272176793695)
      ·
        refine ⟨15177812304001908265190543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10118541536001272176793695 15177812304001908265190543)
        ·
          refine ⟨22766718456002862397785815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15177812304001908265190543 22766718456002862397785815)
          ·
            refine ⟨34150077684004293596678723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22766718456002862397785815 34150077684004293596678723)
            ·
              refine ⟨51225116526006440395018085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34150077684004293596678723 51225116526006440395018085)
              ·
                refine ⟨9604709348626207574065891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51225116526006440395018085 9604709348626207574065891)
                ·
                  refine ⟨14407064022939311361098837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9604709348626207574065891 14407064022939311361098837)
                  ·
                    refine ⟨168832781518820055012877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 14407064022939311361098837 168832781518820055012877)
                    ·
                      rfl

theorem cell22_493201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 8].length) (baseStart_493201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_493201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_493201 prefixEnd_493201 := by exact prefixLift 493201
  have htrace : WordTrace (prefixWord ++ tailWord_493201) baseStart_493201 baseEnd_493201 := by
    simpa [prefixWord, tailWord_493201, baseEnd_493201] using wordTrace_append hprefix tailTrace_493201
  have hstable : (prefixWord ++ tailWord_493201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493201).length < 2 ^ (prefixWord ++ tailWord_493201).sum := by decide
  have hdescent : baseEnd_493201 < baseStart_493201 := by decide
  rcases family_descends (prefixWord ++ tailWord_493201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493220 : List Nat := [2, 3, 1, 2, 2, 2, 1, 3, 3, 3]
def baseStart_493220 : Nat := 118140960795 + 493220 * 2 ^ 59
def prefixEnd_493220 : Nat := 4983230072969 + 3 ^ 40 * 493220 * 2
def baseEnd_493220 : Nat := 168839285607110338787819

theorem tailTrace_493220 : CollatzResearch.WordTrace tailWord_493220 prefixEnd_493220 168839285607110338787819 := by
  unfold tailWord_493220
  simp only [CollatzResearch.WordTrace]
  refine ⟨8994605636577825057398557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11992807515437100076531409 8994605636577825057398557)
  ·
    refine ⟨3372977113716684396524459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8994605636577825057398557 3372977113716684396524459)
    ·
      refine ⟨5059465670575026594786689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3372977113716684396524459 5059465670575026594786689)
      ·
        refine ⟨3794599252931269946090017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5059465670575026594786689 3794599252931269946090017)
        ·
          refine ⟨2845949439698452459567513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3794599252931269946090017 2845949439698452459567513)
          ·
            refine ⟨2134462079773839344675635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2845949439698452459567513 2134462079773839344675635)
            ·
              refine ⟨3201693119660759017013453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2134462079773839344675635 3201693119660759017013453)
              ·
                refine ⟨1200634919872784631380045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3201693119660759017013453 1200634919872784631380045)
                ·
                  refine ⟨450238094952294236767517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1200634919872784631380045 450238094952294236767517)
                  ·
                    refine ⟨168839285607110338787819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 450238094952294236767517 168839285607110338787819)
                    ·
                      rfl

theorem cell22_493220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 3, 3, 3].length) (baseStart_493220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_493220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_493220 prefixEnd_493220 := by exact prefixLift 493220
  have htrace : WordTrace (prefixWord ++ tailWord_493220) baseStart_493220 baseEnd_493220 := by
    simpa [prefixWord, tailWord_493220, baseEnd_493220] using wordTrace_append hprefix tailTrace_493220
  have hstable : (prefixWord ++ tailWord_493220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493220).length < 2 ^ (prefixWord ++ tailWord_493220).sum := by decide
  have hdescent : baseEnd_493220 < baseStart_493220 := by decide
  rcases family_descends (prefixWord ++ tailWord_493220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493297 : List Nat := [1, 2, 2, 2, 2, 5, 1, 2, 1, 4]
def baseStart_493297 : Nat := 118140960795 + 493297 * 2 ^ 59
def prefixEnd_493297 : Nat := 4983230072969 + 3 ^ 40 * 493297 * 2
def baseEnd_493297 : Nat := 168865644280707804612583

theorem tailTrace_493297 : CollatzResearch.WordTrace tailWord_493297 prefixEnd_493297 168865644280707804612583 := by
  unfold tailWord_493297
  simp only [CollatzResearch.WordTrace]
  refine ⟨17992019693876692265350145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11994679795917794843566763 17992019693876692265350145)
  ·
    refine ⟨13494014770407519199012609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17992019693876692265350145 13494014770407519199012609)
    ·
      refine ⟨10120511077805639399259457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13494014770407519199012609 10120511077805639399259457)
      ·
        refine ⟨7590383308354229549444593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10120511077805639399259457 7590383308354229549444593)
        ·
          refine ⟨5692787481265672162083445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7590383308354229549444593 5692787481265672162083445)
          ·
            refine ⟨533698826368656765195323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5692787481265672162083445 533698826368656765195323)
            ·
              refine ⟨800548239552985147792985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 533698826368656765195323 800548239552985147792985)
              ·
                refine ⟨600411179664738860844739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 800548239552985147792985 600411179664738860844739)
                ·
                  refine ⟨900616769497108291267109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 600411179664738860844739 900616769497108291267109)
                  ·
                    refine ⟨168865644280707804612583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 900616769497108291267109 168865644280707804612583)
                    ·
                      rfl

theorem cell22_493297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 2, 1, 4].length) (baseStart_493297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_493297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_493297 prefixEnd_493297 := by exact prefixLift 493297
  have htrace : WordTrace (prefixWord ++ tailWord_493297) baseStart_493297 baseEnd_493297 := by
    simpa [prefixWord, tailWord_493297, baseEnd_493297] using wordTrace_append hprefix tailTrace_493297
  have hstable : (prefixWord ++ tailWord_493297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493297).length < 2 ^ (prefixWord ++ tailWord_493297).sum := by decide
  have hdescent : baseEnd_493297 < baseStart_493297 := by decide
  rcases family_descends (prefixWord ++ tailWord_493297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493314 : List Nat := [3, 4, 1, 1, 1, 1, 5, 1, 1, 4]
def baseStart_493314 : Nat := 118140960795 + 493314 * 2 ^ 59
def prefixEnd_493314 : Nat := 4983230072969 + 3 ^ 40 * 493314 * 2
def baseEnd_493314 : Nat := 168871463728125426937531

theorem tailTrace_493314 : CollatzResearch.WordTrace tailWord_493314 prefixEnd_493314 168871463728125426937531 := by
  unfold tailWord_493314
  simp only [CollatzResearch.WordTrace]
  refine ⟨4498159933703776042179749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11995093156543402779145997 4498159933703776042179749)
  ·
    refine ⟨843404987569458007908703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4498159933703776042179749 843404987569458007908703)
    ·
      refine ⟨1265107481354187011863055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 843404987569458007908703 1265107481354187011863055)
      ·
        refine ⟨1897661222031280517794583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1265107481354187011863055 1897661222031280517794583)
        ·
          refine ⟨2846491833046920776691875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1897661222031280517794583 2846491833046920776691875)
          ·
            refine ⟨4269737749570381165037813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2846491833046920776691875 4269737749570381165037813)
            ·
              refine ⟨400287914022223234222295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4269737749570381165037813 400287914022223234222295)
              ·
                refine ⟨600431871033334851333443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 400287914022223234222295 600431871033334851333443)
                ·
                  refine ⟨900647806550002277000165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 600431871033334851333443 900647806550002277000165)
                  ·
                    refine ⟨168871463728125426937531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 900647806550002277000165 168871463728125426937531)
                    ·
                      rfl

theorem cell22_493314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_493314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_493314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_493314 prefixEnd_493314 := by exact prefixLift 493314
  have htrace : WordTrace (prefixWord ++ tailWord_493314) baseStart_493314 baseEnd_493314 := by
    simpa [prefixWord, tailWord_493314, baseEnd_493314] using wordTrace_append hprefix tailTrace_493314
  have hstable : (prefixWord ++ tailWord_493314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493314).length < 2 ^ (prefixWord ++ tailWord_493314).sum := by decide
  have hdescent : baseEnd_493314 < baseStart_493314 := by decide
  rcases family_descends (prefixWord ++ tailWord_493314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493389 : List Nat := [1, 6, 1, 2, 1, 1, 1, 3, 3, 3]
def baseStart_493389 : Nat := 118140960795 + 493389 * 2 ^ 59
def prefixEnd_493389 : Nat := 4983230072969 + 3 ^ 40 * 493389 * 2
def baseEnd_493389 : Nat := 168897137760850231312301

theorem tailTrace_493389 : CollatzResearch.WordTrace tailWord_493389 prefixEnd_493389 168897137760850231312301 := by
  unfold tailWord_493389
  simp only [CollatzResearch.WordTrace]
  refine ⟨17995375209543391977699221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11996916806362261318466147 17995375209543391977699221)
  ·
    refine ⟨843533212947346498954651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17995375209543391977699221 843533212947346498954651)
    ·
      refine ⟨1265299819421019748431977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 843533212947346498954651 1265299819421019748431977)
      ·
        refine ⟨948974864565764811323983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1265299819421019748431977 948974864565764811323983)
        ·
          refine ⟨1423462296848647216985975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 948974864565764811323983 1423462296848647216985975)
          ·
            refine ⟨2135193445272970825478963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1423462296848647216985975 2135193445272970825478963)
            ·
              refine ⟨3202790167909456238218445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2135193445272970825478963 3202790167909456238218445)
              ·
                refine ⟨1201046312966046089331917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3202790167909456238218445 1201046312966046089331917)
                ·
                  refine ⟨450392367362267283499469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1201046312966046089331917 450392367362267283499469)
                  ·
                    refine ⟨168897137760850231312301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 450392367362267283499469 168897137760850231312301)
                    ·
                      rfl

theorem cell22_493389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_493389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_493389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_493389 prefixEnd_493389 := by exact prefixLift 493389
  have htrace : WordTrace (prefixWord ++ tailWord_493389) baseStart_493389 baseEnd_493389 := by
    simpa [prefixWord, tailWord_493389, baseEnd_493389] using wordTrace_append hprefix tailTrace_493389
  have hstable : (prefixWord ++ tailWord_493389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493389).length < 2 ^ (prefixWord ++ tailWord_493389).sum := by decide
  have hdescent : baseEnd_493389 < baseStart_493389 := by decide
  rcases family_descends (prefixWord ++ tailWord_493389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493402 : List Nat := [3, 1, 1, 2, 1, 3, 5, 1, 5]
def baseStart_493402 : Nat := 118140960795 + 493402 * 2 ^ 59
def prefixEnd_493402 : Nat := 4983230072969 + 3 ^ 40 * 493402 * 2
def baseEnd_493402 : Nat := 56300529308840843579087

theorem tailTrace_493402 : CollatzResearch.WordTrace tailWord_493402 prefixEnd_493402 56300529308840843579087 := by
  unfold tailWord_493402
  simp only [CollatzResearch.WordTrace]
  refine ⟨4498962339624073799480615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11997232905664196798614973 4498962339624073799480615)
  ·
    refine ⟨6748443509436110699220923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4498962339624073799480615 6748443509436110699220923)
    ·
      refine ⟨10122665264154166048831385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6748443509436110699220923 10122665264154166048831385)
      ·
        refine ⟨7591998948115624536623539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10122665264154166048831385 7591998948115624536623539)
        ·
          refine ⟨11387998422173436804935309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7591998948115624536623539 11387998422173436804935309)
          ·
            refine ⟨4270499408315038801850741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11387998422173436804935309 4270499408315038801850741)
            ·
              refine ⟨400359319529534887673507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4270499408315038801850741 400359319529534887673507)
              ·
                refine ⟨600538979294302331510261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 400359319529534887673507 600538979294302331510261)
                ·
                  refine ⟨56300529308840843579087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 600538979294302331510261 56300529308840843579087)
                  ·
                    rfl

theorem cell22_493402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5, 1, 5].length) (baseStart_493402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_493402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_493402 prefixEnd_493402 := by exact prefixLift 493402
  have htrace : WordTrace (prefixWord ++ tailWord_493402) baseStart_493402 baseEnd_493402 := by
    simpa [prefixWord, tailWord_493402, baseEnd_493402] using wordTrace_append hprefix tailTrace_493402
  have hstable : (prefixWord ++ tailWord_493402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493402).length < 2 ^ (prefixWord ++ tailWord_493402).sum := by decide
  have hdescent : baseEnd_493402 < baseStart_493402 := by decide
  rcases family_descends (prefixWord ++ tailWord_493402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493492 : List Nat := [2, 5, 2, 1, 12]
def baseStart_493492 : Nat := 118140960795 + 493492 * 2 ^ 59
def prefixEnd_493492 : Nat := 4983230072969 + 3 ^ 40 * 493492 * 2
def baseEnd_493492 : Nat := 695195048418898337395

theorem tailTrace_493492 : CollatzResearch.WordTrace tailWord_493492 prefixEnd_493492 695195048418898337395 := by
  unfold tailWord_493492
  simp only [CollatzResearch.WordTrace]
  refine ⟨8999565964085120284349365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11999421285446827045799153 8999565964085120284349365)
  ·
    refine ⟨843709309132980026657753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8999565964085120284349365 843709309132980026657753)
    ·
      refine ⟨632781981849735019993315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 843709309132980026657753 632781981849735019993315)
      ·
        refine ⟨949172972774602529989973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 632781981849735019993315 949172972774602529989973)
        ·
          refine ⟨695195048418898337395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 949172972774602529989973 695195048418898337395)
          ·
            rfl

theorem cell22_493492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 12].length) (baseStart_493492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_493492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_493492 prefixEnd_493492 := by exact prefixLift 493492
  have htrace : WordTrace (prefixWord ++ tailWord_493492) baseStart_493492 baseEnd_493492 := by
    simpa [prefixWord, tailWord_493492, baseEnd_493492] using wordTrace_append hprefix tailTrace_493492
  have hstable : (prefixWord ++ tailWord_493492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493492).length < 2 ^ (prefixWord ++ tailWord_493492).sum := by decide
  have hdescent : baseEnd_493492 < baseStart_493492 := by decide
  rcases family_descends (prefixWord ++ tailWord_493492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493524 : List Nat := [2, 4, 1, 2, 1, 1, 3, 2, 3, 3]
def baseStart_493524 : Nat := 118140960795 + 493524 * 2 ^ 59
def prefixEnd_493524 : Nat := 4983230072969 + 3 ^ 40 * 493524 * 2
def baseEnd_493524 : Nat := 168943351019754879186887

theorem tailTrace_493524 : CollatzResearch.WordTrace tailWord_493524 prefixEnd_493524 168943351019754879186887 := by
  unfold tailWord_493524
  simp only [CollatzResearch.WordTrace]
  refine ⟨9000149532027155016931813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12000199376036206689242417 9000149532027155016931813)
  ·
    refine ⟨1687528037255091565674715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9000149532027155016931813 1687528037255091565674715)
    ·
      refine ⟨2531292055882637348512073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1687528037255091565674715 2531292055882637348512073)
      ·
        refine ⟨1898469041911978011384055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2531292055882637348512073 1898469041911978011384055)
        ·
          refine ⟨2847703562867967017076083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1898469041911978011384055 2847703562867967017076083)
          ·
            refine ⟨4271555344301950525614125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2847703562867967017076083 4271555344301950525614125)
            ·
              refine ⟨1601833254113231447105297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4271555344301950525614125 1601833254113231447105297)
              ·
                refine ⟨1201374940584923585328973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1601833254113231447105297 1201374940584923585328973)
                ·
                  refine ⟨450515602719346344498365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1201374940584923585328973 450515602719346344498365)
                  ·
                    refine ⟨168943351019754879186887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 450515602719346344498365 168943351019754879186887)
                    ·
                      rfl

theorem cell22_493524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_493524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_493524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_493524 prefixEnd_493524 := by exact prefixLift 493524
  have htrace : WordTrace (prefixWord ++ tailWord_493524) baseStart_493524 baseEnd_493524 := by
    simpa [prefixWord, tailWord_493524, baseEnd_493524] using wordTrace_append hprefix tailTrace_493524
  have hstable : (prefixWord ++ tailWord_493524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493524).length < 2 ^ (prefixWord ++ tailWord_493524).sum := by decide
  have hdescent : baseEnd_493524 < baseStart_493524 := by decide
  rcases family_descends (prefixWord ++ tailWord_493524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493526 : List Nat := [5, 2, 1, 1, 3, 1, 3, 6]
def baseStart_493526 : Nat := 118140960795 + 493526 * 2 ^ 59
def prefixEnd_493526 : Nat := 4983230072969 + 3 ^ 40 * 493526 * 2
def baseEnd_493526 : Nat := 18771559517847504515209

theorem tailTrace_493526 : CollatzResearch.WordTrace tailWord_493526 prefixEnd_493526 18771559517847504515209 := by
  unfold tailWord_493526
  simp only [CollatzResearch.WordTrace]
  refine ⟨1125023250627941523464777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12000248006698042916957621 1125023250627941523464777)
  ·
    refine ⟨843767437970956142598583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1125023250627941523464777 843767437970956142598583)
    ·
      refine ⟨1265651156956434213897875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 843767437970956142598583 1265651156956434213897875)
      ·
        refine ⟨1898476735434651320846813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1265651156956434213897875 1898476735434651320846813)
        ·
          refine ⟨711928775787994245317555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1898476735434651320846813 711928775787994245317555)
          ·
            refine ⟨1067893163681991367976333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 711928775787994245317555 1067893163681991367976333)
            ·
              refine ⟨400459936380746762991125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1067893163681991367976333 400459936380746762991125)
              ·
                refine ⟨18771559517847504515209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 400459936380746762991125 18771559517847504515209)
                ·
                  rfl

theorem cell22_493526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 3, 6].length) (baseStart_493526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_493526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_493526 prefixEnd_493526 := by exact prefixLift 493526
  have htrace : WordTrace (prefixWord ++ tailWord_493526) baseStart_493526 baseEnd_493526 := by
    simpa [prefixWord, tailWord_493526, baseEnd_493526] using wordTrace_append hprefix tailTrace_493526
  have hstable : (prefixWord ++ tailWord_493526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493526).length < 2 ^ (prefixWord ++ tailWord_493526).sum := by decide
  have hdescent : baseEnd_493526 < baseStart_493526 := by decide
  rcases family_descends (prefixWord ++ tailWord_493526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493582 : List Nat := [4, 1, 1, 2, 2, 1, 1, 4, 6]
def baseStart_493582 : Nat := 118140960795 + 493582 * 2 ^ 59
def prefixEnd_493582 : Nat := 4983230072969 + 3 ^ 40 * 493582 * 2
def baseEnd_493582 : Nat := 56321068535020687078903

theorem tailTrace_493582 : CollatzResearch.WordTrace tailWord_493582 prefixEnd_493582 56321068535020687078903 := by
  unfold tailWord_493582
  simp only [CollatzResearch.WordTrace]
  refine ⟨2250301812230523242434375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12001609665229457292983333 2250301812230523242434375)
  ·
    refine ⟨3375452718345784863651563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2250301812230523242434375 3375452718345784863651563)
    ·
      refine ⟨5063179077518677295477345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3375452718345784863651563 5063179077518677295477345)
      ·
        refine ⟨3797384308139007971608009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5063179077518677295477345 3797384308139007971608009)
        ·
          refine ⟨2848038231104255978706007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3797384308139007971608009 2848038231104255978706007)
          ·
            refine ⟨4272057346656383968059011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2848038231104255978706007 4272057346656383968059011)
            ·
              refine ⟨6408086019984575952088517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4272057346656383968059011 6408086019984575952088517)
              ·
                refine ⟨1201516128747107991016597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6408086019984575952088517 1201516128747107991016597)
                ·
                  refine ⟨56321068535020687078903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1201516128747107991016597 56321068535020687078903)
                  ·
                    rfl

theorem cell22_493582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 4, 6].length) (baseStart_493582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_493582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_493582 prefixEnd_493582 := by exact prefixLift 493582
  have htrace : WordTrace (prefixWord ++ tailWord_493582) baseStart_493582 baseEnd_493582 := by
    simpa [prefixWord, tailWord_493582, baseEnd_493582] using wordTrace_append hprefix tailTrace_493582
  have hstable : (prefixWord ++ tailWord_493582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493582).length < 2 ^ (prefixWord ++ tailWord_493582).sum := by decide
  have hdescent : baseEnd_493582 < baseStart_493582 := by decide
  rcases family_descends (prefixWord ++ tailWord_493582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493616 : List Nat := [2, 1, 1, 1, 2, 6, 3, 2, 4]
def baseStart_493616 : Nat := 118140960795 + 493616 * 2 ^ 59
def prefixEnd_493616 : Nat := 4983230072969 + 3 ^ 40 * 493616 * 2
def baseEnd_493616 : Nat := 56324948166632435295535

theorem tailTrace_493616 : CollatzResearch.WordTrace tailWord_493616 prefixEnd_493616 56324948166632435295535 := by
  unfold tailWord_493616
  simp only [CollatzResearch.WordTrace]
  refine ⟨9001827289860504873106351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12002436386480673164141801 9001827289860504873106351)
  ·
    refine ⟨13502740934790757309659527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9001827289860504873106351 13502740934790757309659527)
    ·
      refine ⟨20254111402186135964489291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13502740934790757309659527 20254111402186135964489291)
      ·
        refine ⟨30381167103279203946733937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20254111402186135964489291 30381167103279203946733937)
        ·
          refine ⟨22785875327459402960050453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30381167103279203946733937 22785875327459402960050453)
          ·
            refine ⟨1068087905974659513752365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 22785875327459402960050453 1068087905974659513752365)
            ·
              refine ⟨400532964740497317657137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1068087905974659513752365 400532964740497317657137)
              ·
                refine ⟨300399723555372988242853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 400532964740497317657137 300399723555372988242853)
                ·
                  refine ⟨56324948166632435295535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 300399723555372988242853 56324948166632435295535)
                  ·
                    rfl

theorem cell22_493616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 3, 2, 4].length) (baseStart_493616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_493616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_493616 prefixEnd_493616 := by exact prefixLift 493616
  have htrace : WordTrace (prefixWord ++ tailWord_493616) baseStart_493616 baseEnd_493616 := by
    simpa [prefixWord, tailWord_493616, baseEnd_493616] using wordTrace_append hprefix tailTrace_493616
  have hstable : (prefixWord ++ tailWord_493616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493616).length < 2 ^ (prefixWord ++ tailWord_493616).sum := by decide
  have hdescent : baseEnd_493616 < baseStart_493616 := by decide
  rcases family_descends (prefixWord ++ tailWord_493616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493631 : List Nat := [1, 1, 2, 2, 3, 1, 6, 1, 2, 3]
def baseStart_493631 : Nat := 118140960795 + 493631 * 2 ^ 59
def prefixEnd_493631 : Nat := 4983230072969 + 3 ^ 40 * 493631 * 2
def baseEnd_493631 : Nat := 168979979306442266761559

theorem tailTrace_493631 : CollatzResearch.WordTrace tailWord_493631 prefixEnd_493631 168979979306442266761559 := by
  unfold tailWord_493631
  simp only [CollatzResearch.WordTrace]
  refine ⟨18004201674666667308008747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12002801116444444872005831 18004201674666667308008747)
  ·
    refine ⟨27006302512000000962013121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18004201674666667308008747 27006302512000000962013121)
    ·
      refine ⟨20254726884000000721509841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27006302512000000962013121 20254726884000000721509841)
      ·
        refine ⟨15191045163000000541132381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20254726884000000721509841 15191045163000000541132381)
        ·
          refine ⟨5696641936125000202924643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15191045163000000541132381 5696641936125000202924643)
          ·
            refine ⟨8544962904187500304386965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5696641936125000202924643 8544962904187500304386965)
            ·
              refine ⟨400545136133789076768139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8544962904187500304386965 400545136133789076768139)
              ·
                refine ⟨600817704200683615152209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 400545136133789076768139 600817704200683615152209)
                ·
                  refine ⟨450613278150512711364157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 600817704200683615152209 450613278150512711364157)
                  ·
                    refine ⟨168979979306442266761559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 450613278150512711364157 168979979306442266761559)
                    ·
                      rfl

theorem cell22_493631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6, 1, 2, 3].length) (baseStart_493631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_493631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_493631 prefixEnd_493631 := by exact prefixLift 493631
  have htrace : WordTrace (prefixWord ++ tailWord_493631) baseStart_493631 baseEnd_493631 := by
    simpa [prefixWord, tailWord_493631, baseEnd_493631] using wordTrace_append hprefix tailTrace_493631
  have hstable : (prefixWord ++ tailWord_493631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493631).length < 2 ^ (prefixWord ++ tailWord_493631).sum := by decide
  have hdescent : baseEnd_493631 < baseStart_493631 := by decide
  rcases family_descends (prefixWord ++ tailWord_493631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493687 : List Nat := [1, 1, 3, 1, 1, 5, 1, 1, 1, 7]
def baseStart_493687 : Nat := 118140960795 + 493687 * 2 ^ 59
def prefixEnd_493687 : Nat := 4983230072969 + 3 ^ 40 * 493687 * 2
def baseEnd_493687 : Nat := 168999149250876787361387

theorem tailTrace_493687 : CollatzResearch.WordTrace tailWord_493687 prefixEnd_493687 168999149250876787361387 := by
  unfold tailWord_493687
  simp only [CollatzResearch.WordTrace]
  refine ⟨18006244162463788872047315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12004162774975859248031543 18006244162463788872047315)
  ·
    refine ⟨27009366243695683308070973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18006244162463788872047315 27009366243695683308070973)
    ·
      refine ⟨10128512341385881240526615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27009366243695683308070973 10128512341385881240526615)
      ·
        refine ⟨15192768512078821860789923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10128512341385881240526615 15192768512078821860789923)
        ·
          refine ⟨22789152768118232791184885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15192768512078821860789923 22789152768118232791184885)
          ·
            refine ⟨2136483072011084324173583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22789152768118232791184885 2136483072011084324173583)
            ·
              refine ⟨3204724608016626486260375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2136483072011084324173583 3204724608016626486260375)
              ·
                refine ⟨4807086912024939729390563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3204724608016626486260375 4807086912024939729390563)
                ·
                  refine ⟨7210630368037409594085845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4807086912024939729390563 7210630368037409594085845)
                  ·
                    refine ⟨168999149250876787361387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7210630368037409594085845 168999149250876787361387)
                    ·
                      rfl

theorem cell22_493687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 7].length) (baseStart_493687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_493687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_493687 prefixEnd_493687 := by exact prefixLift 493687
  have htrace : WordTrace (prefixWord ++ tailWord_493687) baseStart_493687 baseEnd_493687 := by
    simpa [prefixWord, tailWord_493687, baseEnd_493687] using wordTrace_append hprefix tailTrace_493687
  have hstable : (prefixWord ++ tailWord_493687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493687).length < 2 ^ (prefixWord ++ tailWord_493687).sum := by decide
  have hdescent : baseEnd_493687 < baseStart_493687 := by decide
  rcases family_descends (prefixWord ++ tailWord_493687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493689 : List Nat := [1, 2, 1, 3, 4, 1, 2, 3, 5]
def baseStart_493689 : Nat := 118140960795 + 493689 * 2 ^ 59
def prefixEnd_493689 : Nat := 4983230072969 + 3 ^ 40 * 493689 * 2
def baseEnd_493689 : Nat := 56333277963916482937127

theorem tailTrace_493689 : CollatzResearch.WordTrace tailWord_493689 prefixEnd_493689 56333277963916482937127 := by
  unfold tailWord_493689
  simp only [CollatzResearch.WordTrace]
  refine ⟨18006317108456543213620121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12004211405637695475746747 18006317108456543213620121)
  ·
    refine ⟨13504737831342407410215091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18006317108456543213620121 13504737831342407410215091)
    ·
      refine ⟨20257106747013611115322637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13504737831342407410215091 20257106747013611115322637)
      ·
        refine ⟨7596415030130104168245989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20257106747013611115322637 7596415030130104168245989)
        ·
          refine ⟨1424327818149394531546123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7596415030130104168245989 1424327818149394531546123)
          ·
            refine ⟨2136491727224091797319185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1424327818149394531546123 2136491727224091797319185)
            ·
              refine ⟨1602368795418068847989389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2136491727224091797319185 1602368795418068847989389)
              ·
                refine ⟨600888298281775817996021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1602368795418068847989389 600888298281775817996021)
                ·
                  refine ⟨56333277963916482937127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 600888298281775817996021 56333277963916482937127)
                  ·
                    rfl

theorem cell22_493689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 3, 5].length) (baseStart_493689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_493689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_493689 prefixEnd_493689 := by exact prefixLift 493689
  have htrace : WordTrace (prefixWord ++ tailWord_493689) baseStart_493689 baseEnd_493689 := by
    simpa [prefixWord, tailWord_493689, baseEnd_493689] using wordTrace_append hprefix tailTrace_493689
  have hstable : (prefixWord ++ tailWord_493689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493689).length < 2 ^ (prefixWord ++ tailWord_493689).sum := by decide
  have hdescent : baseEnd_493689 < baseStart_493689 := by decide
  rcases family_descends (prefixWord ++ tailWord_493689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493710 : List Nat := [4, 1, 1, 3, 3, 1, 2, 3, 1, 3]
def baseStart_493710 : Nat := 118140960795 + 493710 * 2 ^ 59
def prefixEnd_493710 : Nat := 4983230072969 + 3 ^ 40 * 493710 * 2
def baseEnd_493710 : Nat := 169007022620912394036317

theorem tailTrace_493710 : CollatzResearch.WordTrace tailWord_493710 prefixEnd_493710 169007022620912394036317 := by
  unfold tailWord_493710
  simp only [CollatzResearch.WordTrace]
  refine ⟨2250885380172557975016823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12004722027586975866756389 2250885380172557975016823)
  ·
    refine ⟨3376328070258836962525235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2250885380172557975016823 3376328070258836962525235)
    ·
      refine ⟨5064492105388255443787853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3376328070258836962525235 5064492105388255443787853)
      ·
        refine ⟨1899184539520595791420445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5064492105388255443787853 1899184539520595791420445)
        ·
          refine ⟨712194202320223421782667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1899184539520595791420445 712194202320223421782667)
          ·
            refine ⟨1068291303480335132674001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 712194202320223421782667 1068291303480335132674001)
            ·
              refine ⟨801218477610251349505501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1068291303480335132674001 801218477610251349505501)
              ·
                refine ⟨300456929103844256064563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 801218477610251349505501 300456929103844256064563)
                ·
                  refine ⟨450685393655766384096845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 300456929103844256064563 450685393655766384096845)
                  ·
                    refine ⟨169007022620912394036317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 450685393655766384096845 169007022620912394036317)
                    ·
                      rfl

theorem cell22_493710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 3, 1, 3].length) (baseStart_493710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_493710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_493710 prefixEnd_493710 := by exact prefixLift 493710
  have htrace : WordTrace (prefixWord ++ tailWord_493710) baseStart_493710 baseEnd_493710 := by
    simpa [prefixWord, tailWord_493710, baseEnd_493710] using wordTrace_append hprefix tailTrace_493710
  have hstable : (prefixWord ++ tailWord_493710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493710).length < 2 ^ (prefixWord ++ tailWord_493710).sum := by decide
  have hdescent : baseEnd_493710 < baseStart_493710 := by decide
  rcases family_descends (prefixWord ++ tailWord_493710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493717 : List Nat := [1, 3, 2, 1, 1, 1, 3, 2, 8]
def baseStart_493717 : Nat := 118140960795 + 493717 * 2 ^ 59
def prefixEnd_493717 : Nat := 4983230072969 + 3 ^ 40 * 493717 * 2
def baseEnd_493717 : Nat := 56336472954655569703765

theorem tailTrace_493717 : CollatzResearch.WordTrace tailWord_493717 prefixEnd_493717 56336472954655569703765 := by
  unfold tailWord_493717
  simp only [CollatzResearch.WordTrace]
  refine ⟨18007338352355103995639405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12004892234903402663759603 18007338352355103995639405)
  ·
    refine ⟨6752751882133163998364777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18007338352355103995639405 6752751882133163998364777)
    ·
      refine ⟨5064563911599872998773583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6752751882133163998364777 5064563911599872998773583)
      ·
        refine ⟨7596845867399809498160375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5064563911599872998773583 7596845867399809498160375)
        ·
          refine ⟨11395268801099714247240563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7596845867399809498160375 11395268801099714247240563)
          ·
            refine ⟨17092903201649571370860845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11395268801099714247240563 17092903201649571370860845)
            ·
              refine ⟨6409838700618589264072817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17092903201649571370860845 6409838700618589264072817)
              ·
                refine ⟨4807379025463941948054613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6409838700618589264072817 4807379025463941948054613)
                ·
                  refine ⟨56336472954655569703765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4807379025463941948054613 56336472954655569703765)
                  ·
                    rfl

theorem cell22_493717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 8].length) (baseStart_493717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_493717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_493717 prefixEnd_493717 := by exact prefixLift 493717
  have htrace : WordTrace (prefixWord ++ tailWord_493717) baseStart_493717 baseEnd_493717 := by
    simpa [prefixWord, tailWord_493717, baseEnd_493717] using wordTrace_append hprefix tailTrace_493717
  have hstable : (prefixWord ++ tailWord_493717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493717).length < 2 ^ (prefixWord ++ tailWord_493717).sum := by decide
  have hdescent : baseEnd_493717 < baseStart_493717 := by decide
  rcases family_descends (prefixWord ++ tailWord_493717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493800 : List Nat := [2, 1, 4, 1, 2, 4, 2, 1, 2, 3]
def baseStart_493800 : Nat := 118140960795 + 493800 * 2 ^ 59
def prefixEnd_493800 : Nat := 4983230072969 + 3 ^ 40 * 493800 * 2
def baseEnd_493800 : Nat := 169037831460182159286041

theorem tailTrace_493800 : CollatzResearch.WordTrace tailWord_493800 prefixEnd_493800 169037831460182159286041 := by
  unfold tailWord_493800
  simp only [CollatzResearch.WordTrace]
  refine ⟨9005182805527204585455427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12006910407369606113940569 9005182805527204585455427)
  ·
    refine ⟨13507774208290806878183141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9005182805527204585455427 13507774208290806878183141)
    ·
      refine ⟨2532707664054526289659339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13507774208290806878183141 2532707664054526289659339)
      ·
        refine ⟨3799061496081789434489009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2532707664054526289659339 3799061496081789434489009)
        ·
          refine ⟨2849296122061342075866757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3799061496081789434489009 2849296122061342075866757)
          ·
            refine ⟨534243022886501639225017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2849296122061342075866757 534243022886501639225017)
            ·
              refine ⟨400682267164876229418763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 534243022886501639225017 400682267164876229418763)
              ·
                refine ⟨601023400747314344128145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 400682267164876229418763 601023400747314344128145)
                ·
                  refine ⟨450767550560485758096109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 601023400747314344128145 450767550560485758096109)
                  ·
                    refine ⟨169037831460182159286041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 450767550560485758096109 169037831460182159286041)
                    ·
                      rfl

theorem cell22_493800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 2, 1, 2, 3].length) (baseStart_493800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_493800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_493800 prefixEnd_493800 := by exact prefixLift 493800
  have htrace : WordTrace (prefixWord ++ tailWord_493800) baseStart_493800 baseEnd_493800 := by
    simpa [prefixWord, tailWord_493800, baseEnd_493800] using wordTrace_append hprefix tailTrace_493800
  have hstable : (prefixWord ++ tailWord_493800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493800).length < 2 ^ (prefixWord ++ tailWord_493800).sum := by decide
  have hdescent : baseEnd_493800 < baseStart_493800 := by decide
  rcases family_descends (prefixWord ++ tailWord_493800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493841 : List Nat := [1, 2, 2, 1, 1, 6, 2, 2, 5]
def baseStart_493841 : Nat := 118140960795 + 493841 * 2 ^ 59
def prefixEnd_493841 : Nat := 4983230072969 + 3 ^ 40 * 493841 * 2
def baseEnd_493841 : Nat := 56350622199357239670305

theorem tailTrace_493841 : CollatzResearch.WordTrace tailWord_493841 prefixEnd_493841 56350622199357239670305 := by
  unfold tailWord_493841
  simp only [CollatzResearch.WordTrace]
  refine ⟨18011861003905873173153377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12007907335937248782102251 18011861003905873173153377)
  ·
    refine ⟨13508895752929404879865033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18011861003905873173153377 13508895752929404879865033)
    ·
      refine ⟨10131671814697053659898775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13508895752929404879865033 10131671814697053659898775)
      ·
        refine ⟨15197507722045580489848163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10131671814697053659898775 15197507722045580489848163)
        ·
          refine ⟨22796261583068370734772245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15197507722045580489848163 22796261583068370734772245)
          ·
            refine ⟨1068574761706329878192449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 22796261583068370734772245 1068574761706329878192449)
            ·
              refine ⟨801431071279747408644337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1068574761706329878192449 801431071279747408644337)
              ·
                refine ⟨601073303459810556483253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 801431071279747408644337 601073303459810556483253)
                ·
                  refine ⟨56350622199357239670305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 601073303459810556483253 56350622199357239670305)
                  ·
                    rfl

theorem cell22_493841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 2, 5].length) (baseStart_493841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_493841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_493841 prefixEnd_493841 := by exact prefixLift 493841
  have htrace : WordTrace (prefixWord ++ tailWord_493841) baseStart_493841 baseEnd_493841 := by
    simpa [prefixWord, tailWord_493841, baseEnd_493841] using wordTrace_append hprefix tailTrace_493841
  have hstable : (prefixWord ++ tailWord_493841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493841).length < 2 ^ (prefixWord ++ tailWord_493841).sum := by decide
  have hdescent : baseEnd_493841 < baseStart_493841 := by decide
  rcases family_descends (prefixWord ++ tailWord_493841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493845 : List Nat := [1, 3, 2, 1, 2, 1, 6, 2, 1, 3]
def baseStart_493845 : Nat := 118140960795 + 493845 * 2 ^ 59
def prefixEnd_493845 : Nat := 4983230072969 + 3 ^ 40 * 493845 * 2
def baseEnd_493845 : Nat := 169053235879817041910903

theorem tailTrace_493845 : CollatzResearch.WordTrace tailWord_493845 prefixEnd_493845 169053235879817041910903 := by
  unfold tailWord_493845
  simp only [CollatzResearch.WordTrace]
  refine ⟨18012006895891381856298989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12008004597260921237532659 18012006895891381856298989)
  ·
    refine ⟨6754502585959268196112121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18012006895891381856298989 6754502585959268196112121)
    ·
      refine ⟨5065876939469451147084091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6754502585959268196112121 5065876939469451147084091)
      ·
        refine ⟨7598815409204176720626137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5065876939469451147084091 7598815409204176720626137)
        ·
          refine ⟨5699111556903132540469603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7598815409204176720626137 5699111556903132540469603)
          ·
            refine ⟨8548667335354698810704405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5699111556903132540469603 8548667335354698810704405)
            ·
              refine ⟨400718781344751506751769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8548667335354698810704405 400718781344751506751769)
              ·
                refine ⟨300539086008563630063827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 400718781344751506751769 300539086008563630063827)
                ·
                  refine ⟨450808629012845445095741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 300539086008563630063827 450808629012845445095741)
                  ·
                    refine ⟨169053235879817041910903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 450808629012845445095741 169053235879817041910903)
                    ·
                      rfl

theorem cell22_493845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6, 2, 1, 3].length) (baseStart_493845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_493845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_493845 prefixEnd_493845 := by exact prefixLift 493845
  have htrace : WordTrace (prefixWord ++ tailWord_493845) baseStart_493845 baseEnd_493845 := by
    simpa [prefixWord, tailWord_493845, baseEnd_493845] using wordTrace_append hprefix tailTrace_493845
  have hstable : (prefixWord ++ tailWord_493845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493845).length < 2 ^ (prefixWord ++ tailWord_493845).sum := by decide
  have hdescent : baseEnd_493845 < baseStart_493845 := by decide
  rcases family_descends (prefixWord ++ tailWord_493845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493856 : List Nat := [2, 1, 1, 5, 2, 2, 1, 1, 2, 5]
def baseStart_493856 : Nat := 118140960795 + 493856 * 2 ^ 59
def prefixEnd_493856 : Nat := 4983230072969 + 3 ^ 40 * 493856 * 2
def baseEnd_493856 : Nat := 169057001404616679885869

theorem tailTrace_493856 : CollatzResearch.WordTrace tailWord_493856 prefixEnd_493856 169057001404616679885869 := by
  unfold tailWord_493856
  simp only [CollatzResearch.WordTrace]
  refine ⟨9006204049425765367474711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12008272065901020489966281 9006204049425765367474711)
  ·
    refine ⟨13509306074138648051212067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9006204049425765367474711 13509306074138648051212067)
    ·
      refine ⟨20263959111207972076818101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13509306074138648051212067 20263959111207972076818101)
      ·
        refine ⟨1899746166675747382201697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20263959111207972076818101 1899746166675747382201697)
        ·
          refine ⟨1424809625006810536651273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1899746166675747382201697 1424809625006810536651273)
          ·
            refine ⟨1068607218755107902488455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1424809625006810536651273 1068607218755107902488455)
            ·
              refine ⟨1602910828132661853732683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1068607218755107902488455 1602910828132661853732683)
              ·
                refine ⟨2404366242198992780599025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1602910828132661853732683 2404366242198992780599025)
                ·
                  refine ⟨1803274681649244585449269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2404366242198992780599025 1803274681649244585449269)
                  ·
                    refine ⟨169057001404616679885869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1803274681649244585449269 169057001404616679885869)
                    ·
                      rfl

theorem cell22_493856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 2, 5].length) (baseStart_493856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_493856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_493856 prefixEnd_493856 := by exact prefixLift 493856
  have htrace : WordTrace (prefixWord ++ tailWord_493856) baseStart_493856 baseEnd_493856 := by
    simpa [prefixWord, tailWord_493856, baseEnd_493856] using wordTrace_append hprefix tailTrace_493856
  have hstable : (prefixWord ++ tailWord_493856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493856).length < 2 ^ (prefixWord ++ tailWord_493856).sum := by decide
  have hdescent : baseEnd_493856 < baseStart_493856 := by decide
  rcases family_descends (prefixWord ++ tailWord_493856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493892 : List Nat := [2, 3, 4, 1, 3, 1, 1, 2, 5]
def baseStart_493892 : Nat := 118140960795 + 493892 * 2 ^ 59
def prefixEnd_493892 : Nat := 4983230072969 + 3 ^ 40 * 493892 * 2
def baseEnd_493892 : Nat := 56356441646774861995253

theorem tailTrace_493892 : CollatzResearch.WordTrace tailWord_493892 prefixEnd_493892 56356441646774861995253 := by
  unfold tailWord_493892
  simp only [CollatzResearch.WordTrace]
  refine ⟨9006860563360554441629965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12009147417814072588839953 9006860563360554441629965)
  ·
    refine ⟨3377572711260207915611237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9006860563360554441629965 3377572711260207915611237)
    ·
      refine ⟨633294883361288984177107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3377572711260207915611237 633294883361288984177107)
      ·
        refine ⟨949942325041933476265661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 633294883361288984177107 949942325041933476265661)
        ·
          refine ⟨356228371890725053599623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 949942325041933476265661 356228371890725053599623)
          ·
            refine ⟨534342557836087580399435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356228371890725053599623 534342557836087580399435)
            ·
              refine ⟨801513836754131370599153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 534342557836087580399435 801513836754131370599153)
              ·
                refine ⟨601135377565598527949365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 801513836754131370599153 601135377565598527949365)
                ·
                  refine ⟨56356441646774861995253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 601135377565598527949365 56356441646774861995253)
                  ·
                    rfl

theorem cell22_493892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 2, 5].length) (baseStart_493892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_493892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_493892 prefixEnd_493892 := by exact prefixLift 493892
  have htrace : WordTrace (prefixWord ++ tailWord_493892) baseStart_493892 baseEnd_493892 := by
    simpa [prefixWord, tailWord_493892, baseEnd_493892] using wordTrace_append hprefix tailTrace_493892
  have hstable : (prefixWord ++ tailWord_493892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493892).length < 2 ^ (prefixWord ++ tailWord_493892).sum := by decide
  have hdescent : baseEnd_493892 < baseStart_493892 := by decide
  rcases family_descends (prefixWord ++ tailWord_493892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493914 : List Nat := [3, 1, 1, 2, 1, 2, 1, 11]
def baseStart_493914 : Nat := 118140960795 + 493914 * 2 ^ 59
def prefixEnd_493914 : Nat := 4983230072969 + 3 ^ 40 * 493914 * 2
def baseEnd_493914 : Nat := 18786317332213762437299

theorem tailTrace_493914 : CollatzResearch.WordTrace tailWord_493914 prefixEnd_493914 18786317332213762437299 := by
  unfold tailWord_493914
  simp only [CollatzResearch.WordTrace]
  refine ⟨4503630883160351660140199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12009682355094271093707197 4503630883160351660140199)
  ·
    refine ⟨6755446324740527490210299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4503630883160351660140199 6755446324740527490210299)
    ·
      refine ⟨10133169487110791235315449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6755446324740527490210299 10133169487110791235315449)
      ·
        refine ⟨7599877115333093426486587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10133169487110791235315449 7599877115333093426486587)
        ·
          refine ⟨11399815672999640139729881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7599877115333093426486587 11399815672999640139729881)
          ·
            refine ⟨8549861754749730104797411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11399815672999640139729881 8549861754749730104797411)
            ·
              refine ⟨12824792632124595157196117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8549861754749730104797411 12824792632124595157196117)
              ·
                refine ⟨18786317332213762437299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 12824792632124595157196117 18786317332213762437299)
                ·
                  rfl

theorem cell22_493914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 11].length) (baseStart_493914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_493914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_493914 prefixEnd_493914 := by exact prefixLift 493914
  have htrace : WordTrace (prefixWord ++ tailWord_493914) baseStart_493914 baseEnd_493914 := by
    simpa [prefixWord, tailWord_493914, baseEnd_493914] using wordTrace_append hprefix tailTrace_493914
  have hstable : (prefixWord ++ tailWord_493914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493914).length < 2 ^ (prefixWord ++ tailWord_493914).sum := by decide
  have hdescent : baseEnd_493914 < baseStart_493914 := by decide
  rcases family_descends (prefixWord ++ tailWord_493914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493929 : List Nat := [1, 2, 1, 1, 1, 3, 3, 1, 2, 7]
def baseStart_493929 : Nat := 118140960795 + 493929 * 2 ^ 59
def prefixEnd_493929 : Nat := 4983230072969 + 3 ^ 40 * 493929 * 2
def baseEnd_493929 : Nat := 169081990796468822810645

theorem tailTrace_493929 : CollatzResearch.WordTrace tailWord_493929 prefixEnd_493929 169081990796468822810645 := by
  unfold tailWord_493929
  simp only [CollatzResearch.WordTrace]
  refine ⟨18015070627587064202356841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12010047085058042801571227 18015070627587064202356841)
  ·
    refine ⟨13511302970690298151767631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18015070627587064202356841 13511302970690298151767631)
    ·
      refine ⟨20266954456035447227651447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13511302970690298151767631 20266954456035447227651447)
      ·
        refine ⟨30400431684053170841477171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20266954456035447227651447 30400431684053170841477171)
        ·
          refine ⟨45600647526079756262215757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30400431684053170841477171 45600647526079756262215757)
          ·
            refine ⟨17100242822279908598330909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45600647526079756262215757 17100242822279908598330909)
            ·
              refine ⟨6412591058354965724374091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17100242822279908598330909 6412591058354965724374091)
              ·
                refine ⟨9618886587532448586561137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6412591058354965724374091 9618886587532448586561137)
                ·
                  refine ⟨7214164940649336439920853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9618886587532448586561137 7214164940649336439920853)
                  ·
                    refine ⟨169081990796468822810645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7214164940649336439920853 169081990796468822810645)
                    ·
                      rfl

theorem cell22_493929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 7].length) (baseStart_493929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_493929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_493929 prefixEnd_493929 := by exact prefixLift 493929
  have htrace : WordTrace (prefixWord ++ tailWord_493929) baseStart_493929 baseEnd_493929 := by
    simpa [prefixWord, tailWord_493929, baseEnd_493929] using wordTrace_append hprefix tailTrace_493929
  have hstable : (prefixWord ++ tailWord_493929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493929).length < 2 ^ (prefixWord ++ tailWord_493929).sum := by decide
  have hdescent : baseEnd_493929 < baseStart_493929 := by decide
  rcases family_descends (prefixWord ++ tailWord_493929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493954 : List Nat := [3, 4, 2, 1, 2, 1, 3, 2, 4]
def baseStart_493954 : Nat := 118140960795 + 493954 * 2 ^ 59
def prefixEnd_493954 : Nat := 4983230072969 + 3 ^ 40 * 493954 * 2
def baseEnd_493954 : Nat := 56363516269125696978523

theorem tailTrace_493954 : CollatzResearch.WordTrace tailWord_493954 prefixEnd_493954 56363516269125696978523 := by
  unfold tailWord_493954
  simp only [CollatzResearch.WordTrace]
  refine ⟨4503995613124123368004229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12010654968330995648011277 4503995613124123368004229)
  ·
    refine ⟨844499177460773131500793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4503995613124123368004229 844499177460773131500793)
    ·
      refine ⟨633374383095579848625595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 844499177460773131500793 633374383095579848625595)
      ·
        refine ⟨950061574643369772938393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 633374383095579848625595 950061574643369772938393)
        ·
          refine ⟨712546180982527329703795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 950061574643369772938393 712546180982527329703795)
          ·
            refine ⟨1068819271473790994555693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 712546180982527329703795 1068819271473790994555693)
            ·
              refine ⟨400807226802671622958385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1068819271473790994555693 400807226802671622958385)
              ·
                refine ⟨300605420102003717218789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 400807226802671622958385 300605420102003717218789)
                ·
                  refine ⟨56363516269125696978523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 300605420102003717218789 56363516269125696978523)
                  ·
                    rfl

theorem cell22_493954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_493954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_493954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_493954 prefixEnd_493954 := by exact prefixLift 493954
  have htrace : WordTrace (prefixWord ++ tailWord_493954) baseStart_493954 baseEnd_493954 := by
    simpa [prefixWord, tailWord_493954, baseEnd_493954] using wordTrace_append hprefix tailTrace_493954
  have hstable : (prefixWord ++ tailWord_493954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493954).length < 2 ^ (prefixWord ++ tailWord_493954).sum := by decide
  have hdescent : baseEnd_493954 < baseStart_493954 := by decide
  rcases family_descends (prefixWord ++ tailWord_493954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493963 : List Nat := [1, 1, 1, 1, 4, 4, 3, 1, 3, 3]
def baseStart_493963 : Nat := 118140960795 + 493963 * 2 ^ 59
def prefixEnd_493963 : Nat := 4983230072969 + 3 ^ 40 * 493963 * 2
def baseEnd_493963 : Nat := 169093629691304067460541

theorem tailTrace_493963 : CollatzResearch.WordTrace tailWord_493963 prefixEnd_493963 169093629691304067460541 := by
  unfold tailWord_493963
  simp only [CollatzResearch.WordTrace]
  refine ⟨18016310709463888009094543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12010873806309258672729695 18016310709463888009094543)
  ·
    refine ⟨27024466064195832013641815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18016310709463888009094543 27024466064195832013641815)
    ·
      refine ⟨40536699096293748020462723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27024466064195832013641815 40536699096293748020462723)
      ·
        refine ⟨60805048644440622030694085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40536699096293748020462723 60805048644440622030694085)
        ·
          refine ⟨11400946620832616630755141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60805048644440622030694085 11400946620832616630755141)
          ·
            refine ⟨2137677491406115618266589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11400946620832616630755141 2137677491406115618266589)
            ·
              refine ⟨801629059277293356849971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2137677491406115618266589 801629059277293356849971)
              ·
                refine ⟨1202443588915940035274957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 801629059277293356849971 1202443588915940035274957)
                ·
                  refine ⟨450916345843477513228109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1202443588915940035274957 450916345843477513228109)
                  ·
                    refine ⟨169093629691304067460541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 450916345843477513228109 169093629691304067460541)
                    ·
                      rfl

theorem cell22_493963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 1, 3, 3].length) (baseStart_493963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_493963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_493963 prefixEnd_493963 := by exact prefixLift 493963
  have htrace : WordTrace (prefixWord ++ tailWord_493963) baseStart_493963 baseEnd_493963 := by
    simpa [prefixWord, tailWord_493963, baseEnd_493963] using wordTrace_append hprefix tailTrace_493963
  have hstable : (prefixWord ++ tailWord_493963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493963).length < 2 ^ (prefixWord ++ tailWord_493963).sum := by decide
  have hdescent : baseEnd_493963 < baseStart_493963 := by decide
  rcases family_descends (prefixWord ++ tailWord_493963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
