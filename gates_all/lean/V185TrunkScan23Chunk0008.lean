import V185TrunkScan23Chunk0007

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_46730 : List Nat := [3, 1, 2, 3, 2, 2, 1, 2, 3, 2, 2]
def baseStart_46730 : Nat := 118140960795 + 46730 * 2 ^ 59
def prefixEnd_46730 : Nat := 4983230072969 + 3 ^ 40 * 46730 * 2
def baseEnd_46730 : Nat := 23994950984707402360099

theorem tailTrace_46730 : CollatzResearch.WordTrace tailWord_46730 prefixEnd_46730 23994950984707402360099 := by
  unfold tailWord_46730
  simp only [CollatzResearch.WordTrace]
  refine ⟨426095780178166423430411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1136255413808443795814429 426095780178166423430411)
  ·
    refine ⟨639143670267249635145617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 426095780178166423430411 639143670267249635145617)
    ·
      refine ⟨479357752700437226359213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 639143670267249635145617 479357752700437226359213)
      ·
        refine ⟨179759157262663959884705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 479357752700437226359213 179759157262663959884705)
        ·
          refine ⟨134819367946997969913529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179759157262663959884705 134819367946997969913529)
          ·
            refine ⟨101114525960248477435147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134819367946997969913529 101114525960248477435147)
            ·
              refine ⟨151671788940372716152721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101114525960248477435147 151671788940372716152721)
              ·
                refine ⟨113753841705279537114541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 151671788940372716152721 113753841705279537114541)
                ·
                  refine ⟨42657690639479826417953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 113753841705279537114541 42657690639479826417953)
                  ·
                    refine ⟨31993267979609869813465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42657690639479826417953 31993267979609869813465)
                    ·
                      refine ⟨23994950984707402360099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 31993267979609869813465 23994950984707402360099)
                      ·
                        rfl

theorem cell23_46730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_46730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_46730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_46730 prefixEnd_46730 := by exact prefixLift 46730
  have htrace : WordTrace (prefixWord ++ tailWord_46730) baseStart_46730 baseEnd_46730 := by
    simpa [prefixWord, tailWord_46730, baseEnd_46730] using wordTrace_append hprefix tailTrace_46730
  have hstable : (prefixWord ++ tailWord_46730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46730).length < 2 ^ (prefixWord ++ tailWord_46730).sum := by decide
  have hdescent : baseEnd_46730 < baseStart_46730 := by decide
  rcases family_descends (prefixWord ++ tailWord_46730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46750 : List Nat := [4, 3, 1, 1, 1, 3, 1, 3, 1, 2, 3]
def baseStart_46750 : Nat := 118140960795 + 46750 * 2 ^ 59
def prefixEnd_46750 : Nat := 4983230072969 + 3 ^ 40 * 46750 * 2
def baseEnd_46750 : Nat := 24005220597797324110007

theorem tailTrace_46750 : CollatzResearch.WordTrace tailWord_46750 prefixEnd_46750 24005220597797324110007 := by
  unfold tailWord_46750
  simp only [CollatzResearch.WordTrace]
  refine ⟨213139072580026138681213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1136741720426806072966469 213139072580026138681213)
  ·
    refine ⟨79927152217509802005455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213139072580026138681213 79927152217509802005455)
    ·
      refine ⟨119890728326264703008183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79927152217509802005455 119890728326264703008183)
      ·
        refine ⟨179836092489397054512275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119890728326264703008183 179836092489397054512275)
        ·
          refine ⟨269754138734095581768413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179836092489397054512275 269754138734095581768413)
          ·
            refine ⟨101157802025285843163155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 269754138734095581768413 101157802025285843163155)
            ·
              refine ⟨151736703037928764744733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101157802025285843163155 151736703037928764744733)
              ·
                refine ⟨56901263639223286779275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 151736703037928764744733 56901263639223286779275)
                ·
                  refine ⟨85351895458834930168913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56901263639223286779275 85351895458834930168913)
                  ·
                    refine ⟨64013921594126197626685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 85351895458834930168913 64013921594126197626685)
                    ·
                      refine ⟨24005220597797324110007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 64013921594126197626685 24005220597797324110007)
                      ·
                        rfl

theorem cell23_46750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_46750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_46750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_46750 prefixEnd_46750 := by exact prefixLift 46750
  have htrace : WordTrace (prefixWord ++ tailWord_46750) baseStart_46750 baseEnd_46750 := by
    simpa [prefixWord, tailWord_46750, baseEnd_46750] using wordTrace_append hprefix tailTrace_46750
  have hstable : (prefixWord ++ tailWord_46750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46750).length < 2 ^ (prefixWord ++ tailWord_46750).sum := by decide
  have hdescent : baseEnd_46750 < baseStart_46750 := by decide
  rcases family_descends (prefixWord ++ tailWord_46750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46789 : List Nat := [1, 3, 1, 1, 1, 1, 2, 3, 4, 1, 5]
def baseStart_46789 : Nat := 118140960795 + 46789 * 2 ^ 59
def prefixEnd_46789 : Nat := 4983230072969 + 3 ^ 40 * 46789 * 2
def baseEnd_46789 : Nat := 24025246343322671522327

theorem tailTrace_46789 : CollatzResearch.WordTrace tailWord_46789 prefixEnd_46789 24025246343322671522327 := by
  unfold tailWord_46789
  simp only [CollatzResearch.WordTrace]
  refine ⟨1706535027498918770119421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1137690018332612513412947 1706535027498918770119421)
  ·
    refine ⟨639950635312094538794783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1706535027498918770119421 639950635312094538794783)
    ·
      refine ⟨959925952968141808192175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 639950635312094538794783 959925952968141808192175)
      ·
        refine ⟨1439888929452212712288263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 959925952968141808192175 1439888929452212712288263)
        ·
          refine ⟨2159833394178319068432395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1439888929452212712288263 2159833394178319068432395)
          ·
            refine ⟨3239750091267478602648593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2159833394178319068432395 3239750091267478602648593)
            ·
              refine ⟨2429812568450608951986445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3239750091267478602648593 2429812568450608951986445)
              ·
                refine ⟨911179713168978356994917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2429812568450608951986445 911179713168978356994917)
                ·
                  refine ⟨170846196219183441936547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 911179713168978356994917 170846196219183441936547)
                  ·
                    refine ⟨256269294328775162904821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 170846196219183441936547 256269294328775162904821)
                    ·
                      refine ⟨24025246343322671522327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 256269294328775162904821 24025246343322671522327)
                      ·
                        rfl

theorem cell23_46789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 4, 1, 5].length) (baseStart_46789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_46789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_46789 prefixEnd_46789 := by exact prefixLift 46789
  have htrace : WordTrace (prefixWord ++ tailWord_46789) baseStart_46789 baseEnd_46789 := by
    simpa [prefixWord, tailWord_46789, baseEnd_46789] using wordTrace_append hprefix tailTrace_46789
  have hstable : (prefixWord ++ tailWord_46789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46789).length < 2 ^ (prefixWord ++ tailWord_46789).sum := by decide
  have hdescent : baseEnd_46789 < baseStart_46789 := by decide
  rcases family_descends (prefixWord ++ tailWord_46789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46799 : List Nat := [1, 1, 2, 1, 1, 3, 1, 4, 1, 4, 4]
def baseStart_46799 : Nat := 118140960795 + 46799 * 2 ^ 59
def prefixEnd_46799 : Nat := 4983230072969 + 3 ^ 40 * 46799 * 2
def baseEnd_46799 : Nat := 24030381149867632397281

theorem tailTrace_46799 : CollatzResearch.WordTrace tailWord_46799 prefixEnd_46799 24030381149867632397281 := by
  unfold tailWord_46799
  simp only [CollatzResearch.WordTrace]
  refine ⟨1706899757462690477983451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1137933171641793651988967 1706899757462690477983451)
  ·
    refine ⟨2560349636194035716975177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1706899757462690477983451 2560349636194035716975177)
    ·
      refine ⟨1920262227145526787731383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2560349636194035716975177 1920262227145526787731383)
      ·
        refine ⟨2880393340718290181597075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1920262227145526787731383 2880393340718290181597075)
        ·
          refine ⟨4320590011077435272395613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2880393340718290181597075 4320590011077435272395613)
          ·
            refine ⟨1620221254154038227148355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4320590011077435272395613 1620221254154038227148355)
            ·
              refine ⟨2430331881231057340722533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1620221254154038227148355 2430331881231057340722533)
              ·
                refine ⟨455687227730823251385475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2430331881231057340722533 455687227730823251385475)
                ·
                  refine ⟨683530841596234877078213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 455687227730823251385475 683530841596234877078213)
                  ·
                    refine ⟨128162032799294039452165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 683530841596234877078213 128162032799294039452165)
                    ·
                      refine ⟨24030381149867632397281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 128162032799294039452165 24030381149867632397281)
                      ·
                        rfl

theorem cell23_46799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 4, 4].length) (baseStart_46799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_46799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_46799 prefixEnd_46799 := by exact prefixLift 46799
  have htrace : WordTrace (prefixWord ++ tailWord_46799) baseStart_46799 baseEnd_46799 := by
    simpa [prefixWord, tailWord_46799, baseEnd_46799] using wordTrace_append hprefix tailTrace_46799
  have hstable : (prefixWord ++ tailWord_46799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46799).length < 2 ^ (prefixWord ++ tailWord_46799).sum := by decide
  have hdescent : baseEnd_46799 < baseStart_46799 := by decide
  rcases family_descends (prefixWord ++ tailWord_46799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46820 : List Nat := [2, 3, 1, 1, 1, 3, 2, 4, 2, 2, 2]
def baseStart_46820 : Nat := 118140960795 + 46820 * 2 ^ 59
def prefixEnd_46820 : Nat := 4983230072969 + 3 ^ 40 * 46820 * 2
def baseEnd_46820 : Nat := 24041164243612050234685

theorem tailTrace_46820 : CollatzResearch.WordTrace tailWord_46820 prefixEnd_46820 24041164243612050234685 := by
  unfold tailWord_46820
  simp only [CollatzResearch.WordTrace]
  refine ⟨853832845193305532248957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1138443793591074042998609 853832845193305532248957)
  ·
    refine ⟨320187316947489574593359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 853832845193305532248957 320187316947489574593359)
    ·
      refine ⟨480280975421234361890039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320187316947489574593359 480280975421234361890039)
      ·
        refine ⟨720421463131851542835059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 480280975421234361890039 720421463131851542835059)
        ·
          refine ⟨1080632194697777314252589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 720421463131851542835059 1080632194697777314252589)
          ·
            refine ⟨405237073011666492844721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1080632194697777314252589 405237073011666492844721)
            ·
              refine ⟨303927804758749869633541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 405237073011666492844721 303927804758749869633541)
              ·
                refine ⟨56986463392265600556289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 303927804758749869633541 56986463392265600556289)
                ·
                  refine ⟨42739847544199200417217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56986463392265600556289 42739847544199200417217)
                  ·
                    refine ⟨32054885658149400312913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42739847544199200417217 32054885658149400312913)
                    ·
                      refine ⟨24041164243612050234685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 32054885658149400312913 24041164243612050234685)
                      ·
                        rfl

theorem cell23_46820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 4, 2, 2, 2].length) (baseStart_46820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_46820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_46820 prefixEnd_46820 := by exact prefixLift 46820
  have htrace : WordTrace (prefixWord ++ tailWord_46820) baseStart_46820 baseEnd_46820 := by
    simpa [prefixWord, tailWord_46820, baseEnd_46820] using wordTrace_append hprefix tailTrace_46820
  have hstable : (prefixWord ++ tailWord_46820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46820).length < 2 ^ (prefixWord ++ tailWord_46820).sum := by decide
  have hdescent : baseEnd_46820 < baseStart_46820 := by decide
  rcases family_descends (prefixWord ++ tailWord_46820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46826 : List Nat := [3, 1, 3, 1, 1, 1, 5, 1, 7]
def baseStart_46826 : Nat := 118140960795 + 46826 * 2 ^ 59
def prefixEnd_46826 : Nat := 4983230072969 + 3 ^ 40 * 46826 * 2
def baseEnd_46826 : Nat := 2671582791948780751073

theorem tailTrace_46826 : CollatzResearch.WordTrace tailWord_46826 prefixEnd_46826 2671582791948780751073 := by
  unfold tailWord_46826
  simp only [CollatzResearch.WordTrace]
  refine ⟨426971132091218522304083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1138589685576582726144221 426971132091218522304083)
  ·
    refine ⟨640456698136827783456125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 426971132091218522304083 640456698136827783456125)
    ·
      refine ⟨240171261801310418796047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 640456698136827783456125 240171261801310418796047)
      ·
        refine ⟨360256892701965628194071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240171261801310418796047 360256892701965628194071)
        ·
          refine ⟨540385339052948442291107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360256892701965628194071 540385339052948442291107)
          ·
            refine ⟨810578008579422663436661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 540385339052948442291107 810578008579422663436661)
            ·
              refine ⟨75991688304320874697187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 810578008579422663436661 75991688304320874697187)
              ·
                refine ⟨113987532456481312045781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75991688304320874697187 113987532456481312045781)
                ·
                  refine ⟨2671582791948780751073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 113987532456481312045781 2671582791948780751073)
                  ·
                    rfl

theorem cell23_46826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 1, 7].length) (baseStart_46826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_46826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_46826 prefixEnd_46826 := by exact prefixLift 46826
  have htrace : WordTrace (prefixWord ++ tailWord_46826) baseStart_46826 baseEnd_46826 := by
    simpa [prefixWord, tailWord_46826, baseEnd_46826] using wordTrace_append hprefix tailTrace_46826
  have hstable : (prefixWord ++ tailWord_46826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46826).length < 2 ^ (prefixWord ++ tailWord_46826).sum := by decide
  have hdescent : baseEnd_46826 < baseStart_46826 := by decide
  rcases family_descends (prefixWord ++ tailWord_46826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46839 : List Nat := [1, 1, 3, 1, 1, 1, 4, 1, 3, 7]
def baseStart_46839 : Nat := 118140960795 + 46839 * 2 ^ 59
def prefixEnd_46839 : Nat := 4983230072969 + 3 ^ 40 * 46839 * 2
def baseEnd_46839 : Nat := 8016973458682491965699

theorem tailTrace_46839 : CollatzResearch.WordTrace tailWord_46839 prefixEnd_46839 8016973458682491965699 := by
  unfold tailWord_46839
  simp only [CollatzResearch.WordTrace]
  refine ⟨1708358677317777309439571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1138905784878518206293047 1708358677317777309439571)
  ·
    refine ⟨2562538015976665964159357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1708358677317777309439571 2562538015976665964159357)
    ·
      refine ⟨960951755991249736559759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2562538015976665964159357 960951755991249736559759)
      ·
        refine ⟨1441427633986874604839639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 960951755991249736559759 1441427633986874604839639)
        ·
          refine ⟨2162141450980311907259459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1441427633986874604839639 2162141450980311907259459)
          ·
            refine ⟨3243212176470467860889189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2162141450980311907259459 3243212176470467860889189)
            ·
              refine ⟨608102283088212723916723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3243212176470467860889189 608102283088212723916723)
              ·
                refine ⟨912153424632319085875085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 608102283088212723916723 912153424632319085875085)
                ·
                  refine ⟨342057534237119657203157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 912153424632319085875085 342057534237119657203157)
                  ·
                    refine ⟨8016973458682491965699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 342057534237119657203157 8016973458682491965699)
                    ·
                      rfl

theorem cell23_46839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 7].length) (baseStart_46839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_46839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_46839 prefixEnd_46839 := by exact prefixLift 46839
  have htrace : WordTrace (prefixWord ++ tailWord_46839) baseStart_46839 baseEnd_46839 := by
    simpa [prefixWord, tailWord_46839, baseEnd_46839] using wordTrace_append hprefix tailTrace_46839
  have hstable : (prefixWord ++ tailWord_46839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46839).length < 2 ^ (prefixWord ++ tailWord_46839).sum := by decide
  have hdescent : baseEnd_46839 < baseStart_46839 := by decide
  rcases family_descends (prefixWord ++ tailWord_46839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46910 : List Nat := [4, 2, 1, 2, 2, 1, 3, 1, 2, 1, 4]
def baseStart_46910 : Nat := 118140960795 + 46910 * 2 ^ 59
def prefixEnd_46910 : Nat := 4983230072969 + 3 ^ 40 * 46910 * 2
def baseEnd_46910 : Nat := 24087377502516698109271

theorem tailTrace_46910 : CollatzResearch.WordTrace tailWord_46910 prefixEnd_46910 24087377502516698109271 := by
  unfold tailWord_46910
  simp only [CollatzResearch.WordTrace]
  refine ⟨213868532507569554409273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1140632173373704290182789 213868532507569554409273)
  ·
    refine ⟨160401399380677165806955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213868532507569554409273 160401399380677165806955)
    ·
      refine ⟨240602099071015748710433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160401399380677165806955 240602099071015748710433)
      ·
        refine ⟨180451574303261811532825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240602099071015748710433 180451574303261811532825)
        ·
          refine ⟨135338680727446358649619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180451574303261811532825 135338680727446358649619)
          ·
            refine ⟨203008021091169537974429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135338680727446358649619 203008021091169537974429)
            ·
              refine ⟨76128007909188576740411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 203008021091169537974429 76128007909188576740411)
              ·
                refine ⟨114192011863782865110617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76128007909188576740411 114192011863782865110617)
                ·
                  refine ⟨85644008897837148832963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114192011863782865110617 85644008897837148832963)
                  ·
                    refine ⟨128466013346755723249445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 85644008897837148832963 128466013346755723249445)
                    ·
                      refine ⟨24087377502516698109271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 128466013346755723249445 24087377502516698109271)
                      ·
                        rfl

theorem cell23_46910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_46910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_46910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_46910 prefixEnd_46910 := by exact prefixLift 46910
  have htrace : WordTrace (prefixWord ++ tailWord_46910) baseStart_46910 baseEnd_46910 := by
    simpa [prefixWord, tailWord_46910, baseEnd_46910] using wordTrace_append hprefix tailTrace_46910
  have hstable : (prefixWord ++ tailWord_46910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46910).length < 2 ^ (prefixWord ++ tailWord_46910).sum := by decide
  have hdescent : baseEnd_46910 < baseStart_46910 := by decide
  rcases family_descends (prefixWord ++ tailWord_46910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46920 : List Nat := [2, 1, 3, 1, 1, 4, 1, 5, 1, 4]
def baseStart_46920 : Nat := 118140960795 + 46920 * 2 ^ 59
def prefixEnd_46920 : Nat := 4983230072969 + 3 ^ 40 * 46920 * 2
def baseEnd_46920 : Nat := 8030837436353886328075

theorem tailTrace_46920 : CollatzResearch.WordTrace tailWord_46920 prefixEnd_46920 8030837436353886328075 := by
  unfold tailWord_46920
  simp only [CollatzResearch.WordTrace]
  refine ⟨855656495012164071569107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1140875326682885428758809 855656495012164071569107)
  ·
    refine ⟨1283484742518246107353661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 855656495012164071569107 1283484742518246107353661)
    ·
      refine ⟨481306778444342290257623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1283484742518246107353661 481306778444342290257623)
      ·
        refine ⟨721960167666513435386435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 481306778444342290257623 721960167666513435386435)
        ·
          refine ⟨1082940251499770153079653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 721960167666513435386435 1082940251499770153079653)
          ·
            refine ⟨203051297156206903702435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1082940251499770153079653 203051297156206903702435)
            ·
              refine ⟨304576945734310355553653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203051297156206903702435 304576945734310355553653)
              ·
                refine ⟨28554088662591595833155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 304576945734310355553653 28554088662591595833155)
                ·
                  refine ⟨42831132993887393749733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28554088662591595833155 42831132993887393749733)
                  ·
                    refine ⟨8030837436353886328075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42831132993887393749733 8030837436353886328075)
                    ·
                      rfl

theorem cell23_46920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 5, 1, 4].length) (baseStart_46920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_46920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_46920 prefixEnd_46920 := by exact prefixLift 46920
  have htrace : WordTrace (prefixWord ++ tailWord_46920) baseStart_46920 baseEnd_46920 := by
    simpa [prefixWord, tailWord_46920, baseEnd_46920] using wordTrace_append hprefix tailTrace_46920
  have hstable : (prefixWord ++ tailWord_46920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46920).length < 2 ^ (prefixWord ++ tailWord_46920).sum := by decide
  have hdescent : baseEnd_46920 < baseStart_46920 := by decide
  rcases family_descends (prefixWord ++ tailWord_46920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46933 : List Nat := [1, 3, 2, 2, 2, 2, 3, 2, 6]
def baseStart_46933 : Nat := 118140960795 + 46933 * 2 ^ 59
def prefixEnd_46933 : Nat := 4983230072969 + 3 ^ 40 * 46933 * 2
def baseEnd_46933 : Nat := 2677687506396678680185

theorem tailTrace_46933 : CollatzResearch.WordTrace tailWord_46933 prefixEnd_46933 2677687506396678680185 := by
  unfold tailWord_46933
  simp only [CollatzResearch.WordTrace]
  refine ⟨1711787138977231363361453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1141191425984820908907635 1711787138977231363361453)
  ·
    refine ⟨641920177116461761260545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1711787138977231363361453 641920177116461761260545)
    ·
      refine ⟨481440132837346320945409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 641920177116461761260545 481440132837346320945409)
      ·
        refine ⟨361080099628009740709057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 481440132837346320945409 361080099628009740709057)
        ·
          refine ⟨270810074721007305531793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 361080099628009740709057 270810074721007305531793)
          ·
            refine ⟨203107556040755479148845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 270810074721007305531793 203107556040755479148845)
            ·
              refine ⟨76165333515283304680817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 203107556040755479148845 76165333515283304680817)
              ·
                refine ⟨57124000136462478510613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76165333515283304680817 57124000136462478510613)
                ·
                  refine ⟨2677687506396678680185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 57124000136462478510613 2677687506396678680185)
                  ·
                    rfl

theorem cell23_46933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 2, 6].length) (baseStart_46933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_46933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_46933 prefixEnd_46933 := by exact prefixLift 46933
  have htrace : WordTrace (prefixWord ++ tailWord_46933) baseStart_46933 baseEnd_46933 := by
    simpa [prefixWord, tailWord_46933, baseEnd_46933] using wordTrace_append hprefix tailTrace_46933
  have hstable : (prefixWord ++ tailWord_46933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46933).length < 2 ^ (prefixWord ++ tailWord_46933).sum := by decide
  have hdescent : baseEnd_46933 < baseStart_46933 := by decide
  rcases family_descends (prefixWord ++ tailWord_46933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46976 : List Nat := [2, 1, 1, 2, 1, 2, 4, 1, 3, 6]
def baseStart_46976 : Nat := 118140960795 + 46976 * 2 ^ 59
def prefixEnd_46976 : Nat := 4983230072969 + 3 ^ 40 * 46976 * 2
def baseEnd_46976 : Nat := 8040422408571146627989

theorem tailTrace_46976 : CollatzResearch.WordTrace tailWord_46976 prefixEnd_46976 8040422408571146627989 := by
  unfold tailWord_46976
  simp only [CollatzResearch.WordTrace]
  refine ⟨856677738910724853588391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1142236985214299804784521 856677738910724853588391)
  ·
    refine ⟨1285016608366087280382587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 856677738910724853588391 1285016608366087280382587)
    ·
      refine ⟨1927524912549130920573881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1285016608366087280382587 1927524912549130920573881)
      ·
        refine ⟨1445643684411848190430411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1927524912549130920573881 1445643684411848190430411)
        ·
          refine ⟨2168465526617772285645617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1445643684411848190430411 2168465526617772285645617)
          ·
            refine ⟨1626349144963329214234213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2168465526617772285645617 1626349144963329214234213)
            ·
              refine ⟨304940464680624227668915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1626349144963329214234213 304940464680624227668915)
              ·
                refine ⟨457410697020936341503373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 304940464680624227668915 457410697020936341503373)
                ·
                  refine ⟨171529011382851128063765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 457410697020936341503373 171529011382851128063765)
                  ·
                    refine ⟨8040422408571146627989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 171529011382851128063765 8040422408571146627989)
                    ·
                      rfl

theorem cell23_46976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 3, 6].length) (baseStart_46976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_46976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_46976 prefixEnd_46976 := by exact prefixLift 46976
  have htrace : WordTrace (prefixWord ++ tailWord_46976) baseStart_46976 baseEnd_46976 := by
    simpa [prefixWord, tailWord_46976, baseEnd_46976] using wordTrace_append hprefix tailTrace_46976
  have hstable : (prefixWord ++ tailWord_46976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46976).length < 2 ^ (prefixWord ++ tailWord_46976).sum := by decide
  have hdescent : baseEnd_46976 < baseStart_46976 := by decide
  rcases family_descends (prefixWord ++ tailWord_46976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46993 : List Nat := [1, 2, 2, 1, 1, 1, 6, 1, 4, 4]
def baseStart_46993 : Nat := 118140960795 + 46993 * 2 ^ 59
def prefixEnd_46993 : Nat := 4983230072969 + 3 ^ 40 * 46993 * 2
def baseEnd_46993 : Nat := 8043332132279957790463

theorem tailTrace_46993 : CollatzResearch.WordTrace tailWord_46993 prefixEnd_46993 8043332132279957790463 := by
  unfold tailWord_46993
  simp only [CollatzResearch.WordTrace]
  refine ⟨1713975518759861610545633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1142650345839907740363755 1713975518759861610545633)
  ·
    refine ⟨1285481639069896207909225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1713975518759861610545633 1285481639069896207909225)
    ·
      refine ⟨964111229302422155931919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1285481639069896207909225 964111229302422155931919)
      ·
        refine ⟨1446166843953633233897879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 964111229302422155931919 1446166843953633233897879)
        ·
          refine ⟨2169250265930449850846819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1446166843953633233897879 2169250265930449850846819)
          ·
            refine ⟨3253875398895674776270229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2169250265930449850846819 3253875398895674776270229)
            ·
              refine ⟨152525409323234755137667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3253875398895674776270229 152525409323234755137667)
              ·
                refine ⟨228788113984852132706501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152525409323234755137667 228788113984852132706501)
                ·
                  refine ⟨42897771372159774882469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 228788113984852132706501 42897771372159774882469)
                  ·
                    refine ⟨8043332132279957790463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42897771372159774882469 8043332132279957790463)
                    ·
                      rfl

theorem cell23_46993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 4, 4].length) (baseStart_46993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_46993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_46993 prefixEnd_46993 := by exact prefixLift 46993
  have htrace : WordTrace (prefixWord ++ tailWord_46993) baseStart_46993 baseEnd_46993 := by
    simpa [prefixWord, tailWord_46993, baseEnd_46993] using wordTrace_append hprefix tailTrace_46993
  have hstable : (prefixWord ++ tailWord_46993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46993).length < 2 ^ (prefixWord ++ tailWord_46993).sum := by decide
  have hdescent : baseEnd_46993 < baseStart_46993 := by decide
  rcases family_descends (prefixWord ++ tailWord_46993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46994 : List Nat := [3, 2, 3, 2, 1, 3, 1, 1, 3, 1, 3]
def baseStart_46994 : Nat := 118140960795 + 46994 * 2 ^ 59
def prefixEnd_46994 : Nat := 4983230072969 + 3 ^ 40 * 46994 * 2
def baseEnd_46994 : Nat := 24130509877494369458885

theorem tailTrace_46994 : CollatzResearch.WordTrace tailWord_46994 prefixEnd_46994 24130509877494369458885 := by
  unfold tailWord_46994
  simp only [CollatzResearch.WordTrace]
  refine ⟨428502997939059695333009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1142674661170825854221357 428502997939059695333009)
  ·
    refine ⟨321377248454294771499757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 428502997939059695333009 321377248454294771499757)
    ·
      refine ⟨120516468170360539312409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 321377248454294771499757 120516468170360539312409)
      ·
        refine ⟨90387351127770404484307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120516468170360539312409 90387351127770404484307)
        ·
          refine ⟨135581026691655606726461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90387351127770404484307 135581026691655606726461)
          ·
            refine ⟨50842885009370852522423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135581026691655606726461 50842885009370852522423)
            ·
              refine ⟨76264327514056278783635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50842885009370852522423 76264327514056278783635)
              ·
                refine ⟨114396491271084418175453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76264327514056278783635 114396491271084418175453)
                ·
                  refine ⟨42898684226656656815795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114396491271084418175453 42898684226656656815795)
                  ·
                    refine ⟨64348026339984985223693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42898684226656656815795 64348026339984985223693)
                    ·
                      refine ⟨24130509877494369458885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 64348026339984985223693 24130509877494369458885)
                      ·
                        rfl

theorem cell23_46994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_46994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_46994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_46994 prefixEnd_46994 := by exact prefixLift 46994
  have htrace : WordTrace (prefixWord ++ tailWord_46994) baseStart_46994 baseEnd_46994 := by
    simpa [prefixWord, tailWord_46994, baseEnd_46994] using wordTrace_append hprefix tailTrace_46994
  have hstable : (prefixWord ++ tailWord_46994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46994).length < 2 ^ (prefixWord ++ tailWord_46994).sum := by decide
  have hdescent : baseEnd_46994 < baseStart_46994 := by decide
  rcases family_descends (prefixWord ++ tailWord_46994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47050 : List Nat := [3, 1, 2, 1, 2, 1, 2, 3, 4, 1, 3]
def baseStart_47050 : Nat := 118140960795 + 47050 * 2 ^ 59
def prefixEnd_47050 : Nat := 4983230072969 + 3 ^ 40 * 47050 * 2
def baseEnd_47050 : Nat := 24159264794146150358627

theorem tailTrace_47050 : CollatzResearch.WordTrace tailWord_47050 prefixEnd_47050 24159264794146150358627 := by
  unfold tailWord_47050
  simp only [CollatzResearch.WordTrace]
  refine ⟨429013619888340086342651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1144036319702240230247069 429013619888340086342651)
  ·
    refine ⟨643520429832510129513977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 429013619888340086342651 643520429832510129513977)
    ·
      refine ⟨482640322374382597135483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 643520429832510129513977 482640322374382597135483)
      ·
        refine ⟨723960483561573895703225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 482640322374382597135483 723960483561573895703225)
        ·
          refine ⟨542970362671180421777419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 723960483561573895703225 542970362671180421777419)
          ·
            refine ⟨814455544006770632666129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 542970362671180421777419 814455544006770632666129)
            ·
              refine ⟨610841658005077974499597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 814455544006770632666129 610841658005077974499597)
              ·
                refine ⟨229065621751904240437349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 610841658005077974499597 229065621751904240437349)
                ·
                  refine ⟨42949804078482045082003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 229065621751904240437349 42949804078482045082003)
                  ·
                    refine ⟨64424706117723067623005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42949804078482045082003 64424706117723067623005)
                    ·
                      refine ⟨24159264794146150358627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 64424706117723067623005 24159264794146150358627)
                      ·
                        rfl

theorem cell23_47050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 4, 1, 3].length) (baseStart_47050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_47050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_47050 prefixEnd_47050 := by exact prefixLift 47050
  have htrace : WordTrace (prefixWord ++ tailWord_47050) baseStart_47050 baseEnd_47050 := by
    simpa [prefixWord, tailWord_47050, baseEnd_47050] using wordTrace_append hprefix tailTrace_47050
  have hstable : (prefixWord ++ tailWord_47050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47050).length < 2 ^ (prefixWord ++ tailWord_47050).sum := by decide
  have hdescent : baseEnd_47050 < baseStart_47050 := by decide
  rcases family_descends (prefixWord ++ tailWord_47050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47068 : List Nat := [2, 2, 6, 1, 1, 1, 1, 2, 3, 2, 2]
def baseStart_47068 : Nat := 118140960795 + 47068 * 2 ^ 59
def prefixEnd_47068 : Nat := 4983230072969 + 3 ^ 40 * 47068 * 2
def baseEnd_47068 : Nat := 24168507445927079933545

theorem tailTrace_47068 : CollatzResearch.WordTrace tailWord_47068 prefixEnd_47068 24168507445927079933545 := by
  unfold tailWord_47068
  simp only [CollatzResearch.WordTrace]
  refine ⟨858355496744074709762929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1144473995658766279683905 858355496744074709762929)
  ·
    refine ⟨643766622558056032322197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 858355496744074709762929 643766622558056032322197)
    ·
      refine ⟨30176560432408876515103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 643766622558056032322197 30176560432408876515103)
      ·
        refine ⟨45264840648613314772655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30176560432408876515103 45264840648613314772655)
        ·
          refine ⟨67897260972919972158983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45264840648613314772655 67897260972919972158983)
          ·
            refine ⟨101845891459379958238475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67897260972919972158983 101845891459379958238475)
            ·
              refine ⟨152768837189069937357713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101845891459379958238475 152768837189069937357713)
              ·
                refine ⟨114576627891802453018285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152768837189069937357713 114576627891802453018285)
                ·
                  refine ⟨42966235459425919881857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114576627891802453018285 42966235459425919881857)
                  ·
                    refine ⟨32224676594569439911393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42966235459425919881857 32224676594569439911393)
                    ·
                      refine ⟨24168507445927079933545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 32224676594569439911393 24168507445927079933545)
                      ·
                        rfl

theorem cell23_47068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_47068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_47068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_47068 prefixEnd_47068 := by exact prefixLift 47068
  have htrace : WordTrace (prefixWord ++ tailWord_47068) baseStart_47068 baseEnd_47068 := by
    simpa [prefixWord, tailWord_47068, baseEnd_47068] using wordTrace_append hprefix tailTrace_47068
  have hstable : (prefixWord ++ tailWord_47068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47068).length < 2 ^ (prefixWord ++ tailWord_47068).sum := by decide
  have hdescent : baseEnd_47068 < baseStart_47068 := by decide
  rcases family_descends (prefixWord ++ tailWord_47068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47203 : List Nat := [1, 1, 1, 5, 1, 1, 2, 1, 10]
def baseStart_47203 : Nat := 118140960795 + 47203 * 2 ^ 59
def prefixEnd_47203 : Nat := 4983230072969 + 3 ^ 40 * 47203 * 2
def baseEnd_47203 : Nat := 2693091926031561305047

theorem tailTrace_47203 : CollatzResearch.WordTrace tailWord_47203 prefixEnd_47203 2693091926031561305047 := by
  unfold tailWord_47203
  simp only [CollatzResearch.WordTrace]
  refine ⟨1721634847999067475690263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1147756565332711650460175 1721634847999067475690263)
  ·
    refine ⟨2582452271998601213535395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1721634847999067475690263 2582452271998601213535395)
    ·
      refine ⟨3873678407997901820303093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2582452271998601213535395 3873678407997901820303093)
      ·
        refine ⟨363157350749803295653415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3873678407997901820303093 363157350749803295653415)
        ·
          refine ⟨544736026124704943480123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 363157350749803295653415 544736026124704943480123)
          ·
            refine ⟨817104039187057415220185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 544736026124704943480123 817104039187057415220185)
            ·
              refine ⟨612828029390293061415139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 817104039187057415220185 612828029390293061415139)
              ·
                refine ⟨919242044085439592122709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 612828029390293061415139 919242044085439592122709)
                ·
                  refine ⟨2693091926031561305047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 919242044085439592122709 2693091926031561305047)
                  ·
                    rfl

theorem cell23_47203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 10].length) (baseStart_47203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_47203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_47203 prefixEnd_47203 := by exact prefixLift 47203
  have htrace : WordTrace (prefixWord ++ tailWord_47203) baseStart_47203 baseEnd_47203 := by
    simpa [prefixWord, tailWord_47203, baseEnd_47203] using wordTrace_append hprefix tailTrace_47203
  have hstable : (prefixWord ++ tailWord_47203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47203).length < 2 ^ (prefixWord ++ tailWord_47203).sum := by decide
  have hdescent : baseEnd_47203 < baseStart_47203 := by decide
  rcases family_descends (prefixWord ++ tailWord_47203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47271 : List Nat := [1, 1, 6, 2, 3, 1, 1, 2, 6]
def baseStart_47271 : Nat := 118140960795 + 47271 * 2 ^ 59
def prefixEnd_47271 : Nat := 4983230072969 + 3 ^ 40 * 47271 * 2
def baseEnd_47271 : Nat := 2696971557643309521679

theorem tailTrace_47271 : CollatzResearch.WordTrace tailWord_47271 prefixEnd_47271 2696971557643309521679 := by
  unfold tailWord_47271
  simp only [CollatzResearch.WordTrace]
  refine ⟨1724115011752715089165667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1149410007835143392777111 1724115011752715089165667)
  ·
    refine ⟨2586172517629072633748501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1724115011752715089165667 2586172517629072633748501)
    ·
      refine ⟨121226836763862779706961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2586172517629072633748501 121226836763862779706961)
      ·
        refine ⟨90920127572897084780221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121226836763862779706961 90920127572897084780221)
        ·
          refine ⟨34095047839836406792583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90920127572897084780221 34095047839836406792583)
          ·
            refine ⟨51142571759754610188875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34095047839836406792583 51142571759754610188875)
            ·
              refine ⟨76713857639631915283313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51142571759754610188875 76713857639631915283313)
              ·
                refine ⟨57535393229723936462485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76713857639631915283313 57535393229723936462485)
                ·
                  refine ⟨2696971557643309521679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 57535393229723936462485 2696971557643309521679)
                  ·
                    rfl

theorem cell23_47271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 2, 6].length) (baseStart_47271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_47271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_47271 prefixEnd_47271 := by exact prefixLift 47271
  have htrace : WordTrace (prefixWord ++ tailWord_47271) baseStart_47271 baseEnd_47271 := by
    simpa [prefixWord, tailWord_47271, baseEnd_47271] using wordTrace_append hprefix tailTrace_47271
  have hstable : (prefixWord ++ tailWord_47271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47271).length < 2 ^ (prefixWord ++ tailWord_47271).sum := by decide
  have hdescent : baseEnd_47271 < baseStart_47271 := by decide
  rcases family_descends (prefixWord ++ tailWord_47271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47281 : List Nat := [1, 2, 2, 5, 2, 1, 2, 1, 3, 1, 3]
def baseStart_47281 : Nat := 118140960795 + 47281 * 2 ^ 59
def prefixEnd_47281 : Nat := 4983230072969 + 3 ^ 40 * 47281 * 2
def baseEnd_47281 : Nat := 24277878825334746570065

theorem tailTrace_47281 : CollatzResearch.WordTrace tailWord_47281 prefixEnd_47281 24277878825334746570065 := by
  unfold tailWord_47281
  simp only [CollatzResearch.WordTrace]
  refine ⟨1724479741716486797029697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1149653161144324531353131 1724479741716486797029697)
  ·
    refine ⟨1293359806287365097772273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1724479741716486797029697 1293359806287365097772273)
    ·
      refine ⟨970019854715523823329205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1293359806287365097772273 970019854715523823329205)
      ·
        refine ⟨90939361379580358437113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 970019854715523823329205 90939361379580358437113)
        ·
          refine ⟨68204521034685268827835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90939361379580358437113 68204521034685268827835)
          ·
            refine ⟨102306781552027903241753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68204521034685268827835 102306781552027903241753)
            ·
              refine ⟨76730086164020927431315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102306781552027903241753 76730086164020927431315)
              ·
                refine ⟨115095129246031391146973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76730086164020927431315 115095129246031391146973)
                ·
                  refine ⟨43160673467261771680115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 115095129246031391146973 43160673467261771680115)
                  ·
                    refine ⟨64741010200892657520173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43160673467261771680115 64741010200892657520173)
                    ·
                      refine ⟨24277878825334746570065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 64741010200892657520173 24277878825334746570065)
                      ·
                        rfl

theorem cell23_47281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_47281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_47281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_47281 prefixEnd_47281 := by exact prefixLift 47281
  have htrace : WordTrace (prefixWord ++ tailWord_47281) baseStart_47281 baseEnd_47281 := by
    simpa [prefixWord, tailWord_47281, baseEnd_47281] using wordTrace_append hprefix tailTrace_47281
  have hstable : (prefixWord ++ tailWord_47281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47281).length < 2 ^ (prefixWord ++ tailWord_47281).sum := by decide
  have hdescent : baseEnd_47281 < baseStart_47281 := by decide
  rcases family_descends (prefixWord ++ tailWord_47281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47290 : List Nat := [3, 1, 1, 1, 2, 2, 3, 1, 3, 1, 5]
def baseStart_47290 : Nat := 118140960795 + 47290 * 2 ^ 59
def prefixEnd_47290 : Nat := 4983230072969 + 3 ^ 40 * 47290 * 2
def baseEnd_47290 : Nat := 24282500151225211357523

theorem tailTrace_47290 : CollatzResearch.WordTrace tailWord_47290 prefixEnd_47290 24282500151225211357523 := by
  unfold tailWord_47290
  simp only [CollatzResearch.WordTrace]
  refine ⟨431201999670970333526831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1149871999122587556071549 431201999670970333526831)
  ·
    refine ⟨646802999506455500290247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 431201999670970333526831 646802999506455500290247)
    ·
      refine ⟨970204499259683250435371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 646802999506455500290247 970204499259683250435371)
      ·
        refine ⟨1455306748889524875653057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 970204499259683250435371 1455306748889524875653057)
        ·
          refine ⟨1091480061667143656739793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1455306748889524875653057 1091480061667143656739793)
          ·
            refine ⟨818610046250357742554845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1091480061667143656739793 818610046250357742554845)
            ·
              refine ⟨306978767343884153458067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 818610046250357742554845 306978767343884153458067)
              ·
                refine ⟨460468151015826230187101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 306978767343884153458067 460468151015826230187101)
                ·
                  refine ⟨172675556630934836320163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 460468151015826230187101 172675556630934836320163)
                  ·
                    refine ⟨259013334946402254480245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 172675556630934836320163 259013334946402254480245)
                    ·
                      refine ⟨24282500151225211357523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 259013334946402254480245 24282500151225211357523)
                      ·
                        rfl

theorem cell23_47290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 3, 1, 5].length) (baseStart_47290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_47290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_47290 prefixEnd_47290 := by exact prefixLift 47290
  have htrace : WordTrace (prefixWord ++ tailWord_47290) baseStart_47290 baseEnd_47290 := by
    simpa [prefixWord, tailWord_47290, baseEnd_47290] using wordTrace_append hprefix tailTrace_47290
  have hstable : (prefixWord ++ tailWord_47290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47290).length < 2 ^ (prefixWord ++ tailWord_47290).sum := by decide
  have hdescent : baseEnd_47290 < baseStart_47290 := by decide
  rcases family_descends (prefixWord ++ tailWord_47290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47298 : List Nat := [3, 5, 1, 1, 1, 1, 2, 2, 3, 1, 3]
def baseStart_47298 : Nat := 118140960795 + 47298 * 2 ^ 59
def prefixEnd_47298 : Nat := 4983230072969 + 3 ^ 40 * 47298 * 2
def baseEnd_47298 : Nat := 24286607996461180057487

theorem tailTrace_47298 : CollatzResearch.WordTrace tailWord_47298 prefixEnd_47298 24286607996461180057487 := by
  unfold tailWord_47298
  simp only [CollatzResearch.WordTrace]
  refine ⟨431274945663724675099637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1150066521769932466932365 431274945663724675099637)
  ·
    refine ⟨40432026155974188290591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 431274945663724675099637 40432026155974188290591)
    ·
      refine ⟨60648039233961282435887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40432026155974188290591 60648039233961282435887)
      ·
        refine ⟨90972058850941923653831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60648039233961282435887 90972058850941923653831)
        ·
          refine ⟨136458088276412885480747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90972058850941923653831 136458088276412885480747)
          ·
            refine ⟨204687132414619328221121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136458088276412885480747 204687132414619328221121)
            ·
              refine ⟨153515349310964496165841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204687132414619328221121 153515349310964496165841)
              ·
                refine ⟨115136511983223372124381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153515349310964496165841 115136511983223372124381)
                ·
                  refine ⟨43176191993708764546643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 115136511983223372124381 43176191993708764546643)
                  ·
                    refine ⟨64764287990563146819965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43176191993708764546643 64764287990563146819965)
                    ·
                      refine ⟨24286607996461180057487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 64764287990563146819965 24286607996461180057487)
                      ·
                        rfl

theorem cell23_47298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_47298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_47298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_47298 prefixEnd_47298 := by exact prefixLift 47298
  have htrace : WordTrace (prefixWord ++ tailWord_47298) baseStart_47298 baseEnd_47298 := by
    simpa [prefixWord, tailWord_47298, baseEnd_47298] using wordTrace_append hprefix tailTrace_47298
  have hstable : (prefixWord ++ tailWord_47298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47298).length < 2 ^ (prefixWord ++ tailWord_47298).sum := by decide
  have hdescent : baseEnd_47298 < baseStart_47298 := by decide
  rcases family_descends (prefixWord ++ tailWord_47298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47340 : List Nat := [2, 2, 1, 1, 2, 3, 2, 1, 2, 7]
def baseStart_47340 : Nat := 118140960795 + 47340 * 2 ^ 59
def prefixEnd_47340 : Nat := 4983230072969 + 3 ^ 40 * 47340 * 2
def baseEnd_47340 : Nat := 8102724727983338577431

theorem tailTrace_47340 : CollatzResearch.WordTrace tailWord_47340 prefixEnd_47340 8102724727983338577431 := by
  unfold tailWord_47340
  simp only [CollatzResearch.WordTrace]
  refine ⟨863315824251369936713737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1151087765668493248951649 863315824251369936713737)
  ·
    refine ⟨647486868188527452535303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 863315824251369936713737 647486868188527452535303)
    ·
      refine ⟨971230302282791178802955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 647486868188527452535303 971230302282791178802955)
      ·
        refine ⟨1456845453424186768204433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 971230302282791178802955 1456845453424186768204433)
        ·
          refine ⟨1092634090068140076153325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1456845453424186768204433 1092634090068140076153325)
          ·
            refine ⟨409737783775552528557497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1092634090068140076153325 409737783775552528557497)
            ·
              refine ⟨307303337831664396418123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 409737783775552528557497 307303337831664396418123)
              ·
                refine ⟨460955006747496594627185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 307303337831664396418123 460955006747496594627185)
                ·
                  refine ⟨345716255060622445970389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 460955006747496594627185 345716255060622445970389)
                  ·
                    refine ⟨8102724727983338577431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 345716255060622445970389 8102724727983338577431)
                    ·
                      rfl

theorem cell23_47340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 7].length) (baseStart_47340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_47340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_47340 prefixEnd_47340 := by exact prefixLift 47340
  have htrace : WordTrace (prefixWord ++ tailWord_47340) baseStart_47340 baseEnd_47340 := by
    simpa [prefixWord, tailWord_47340, baseEnd_47340] using wordTrace_append hprefix tailTrace_47340
  have hstable : (prefixWord ++ tailWord_47340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47340).length < 2 ^ (prefixWord ++ tailWord_47340).sum := by decide
  have hdescent : baseEnd_47340 < baseStart_47340 := by decide
  rcases family_descends (prefixWord ++ tailWord_47340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47389 : List Nat := [1, 4, 2, 3, 3, 1, 2, 2, 1, 2, 2]
def baseStart_47389 : Nat := 118140960795 + 47389 * 2 ^ 59
def prefixEnd_47389 : Nat := 4983230072969 + 3 ^ 40 * 47389 * 2
def baseEnd_47389 : Nat := 24333334736020324019569

theorem tailTrace_47389 : CollatzResearch.WordTrace tailWord_47389 prefixEnd_47389 24333334736020324019569 := by
  unfold tailWord_47389
  simp only [CollatzResearch.WordTrace]
  refine ⟨1728418825325221241961221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1152279216883480827974147 1728418825325221241961221)
  ·
    refine ⟨324078529748478982867729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1728418825325221241961221 324078529748478982867729)
    ·
      refine ⟨243058897311359237150797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324078529748478982867729 243058897311359237150797)
      ·
        refine ⟨91147086491759713931549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 243058897311359237150797 91147086491759713931549)
        ·
          refine ⟨34180157434409892724331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91147086491759713931549 34180157434409892724331)
          ·
            refine ⟨51270236151614839086497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34180157434409892724331 51270236151614839086497)
            ·
              refine ⟨38452677113711129314873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51270236151614839086497 38452677113711129314873)
              ·
                refine ⟨28839507835283346986155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38452677113711129314873 28839507835283346986155)
                ·
                  refine ⟨43259261752925020479233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28839507835283346986155 43259261752925020479233)
                  ·
                    refine ⟨32444446314693765359425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43259261752925020479233 32444446314693765359425)
                    ·
                      refine ⟨24333334736020324019569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 32444446314693765359425 24333334736020324019569)
                      ·
                        rfl

theorem cell23_47389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_47389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_47389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_47389 prefixEnd_47389 := by exact prefixLift 47389
  have htrace : WordTrace (prefixWord ++ tailWord_47389) baseStart_47389 baseEnd_47389 := by
    simpa [prefixWord, tailWord_47389, baseEnd_47389] using wordTrace_append hprefix tailTrace_47389
  have hstable : (prefixWord ++ tailWord_47389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47389).length < 2 ^ (prefixWord ++ tailWord_47389).sum := by decide
  have hdescent : baseEnd_47389 < baseStart_47389 := by decide
  rcases family_descends (prefixWord ++ tailWord_47389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47411 : List Nat := [1, 1, 1, 2, 5, 1, 1, 5, 2, 2, 2]
def baseStart_47411 : Nat := 118140960795 + 47411 * 2 ^ 59
def prefixEnd_47411 : Nat := 4983230072969 + 3 ^ 40 * 47411 * 2
def baseEnd_47411 : Nat := 24344631310419237944467

theorem tailTrace_47411 : CollatzResearch.WordTrace tailWord_47411 prefixEnd_47411 24344631310419237944467 := by
  unfold tailWord_47411
  simp only [CollatzResearch.WordTrace]
  refine ⟨1729221231245518999262087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1152814154163679332841391 1729221231245518999262087)
  ·
    refine ⟨2593831846868278498893131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1729221231245518999262087 2593831846868278498893131)
    ·
      refine ⟨3890747770302417748339697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2593831846868278498893131 3890747770302417748339697)
      ·
        refine ⟨2918060827726813311254773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3890747770302417748339697 2918060827726813311254773)
        ·
          refine ⟨273568202599388747930135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2918060827726813311254773 273568202599388747930135)
          ·
            refine ⟨410352303899083121895203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273568202599388747930135 410352303899083121895203)
            ·
              refine ⟨615528455848624682842805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 410352303899083121895203 615528455848624682842805)
              ·
                refine ⟨57705792735808564016513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 615528455848624682842805 57705792735808564016513)
                ·
                  refine ⟨43279344551856423012385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57705792735808564016513 43279344551856423012385)
                  ·
                    refine ⟨32459508413892317259289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43279344551856423012385 32459508413892317259289)
                    ·
                      refine ⟨24344631310419237944467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 32459508413892317259289 24344631310419237944467)
                      ·
                        rfl

theorem cell23_47411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 5, 2, 2, 2].length) (baseStart_47411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_47411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_47411 prefixEnd_47411 := by exact prefixLift 47411
  have htrace : WordTrace (prefixWord ++ tailWord_47411) baseStart_47411 baseEnd_47411 := by
    simpa [prefixWord, tailWord_47411, baseEnd_47411] using wordTrace_append hprefix tailTrace_47411
  have hstable : (prefixWord ++ tailWord_47411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47411).length < 2 ^ (prefixWord ++ tailWord_47411).sum := by decide
  have hdescent : baseEnd_47411 < baseStart_47411 := by decide
  rcases family_descends (prefixWord ++ tailWord_47411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47417 : List Nat := [1, 2, 1, 6, 1, 1, 1, 1, 9]
def baseStart_47417 : Nat := 118140960795 + 47417 * 2 ^ 59
def prefixEnd_47417 : Nat := 4983230072969 + 3 ^ 40 * 47417 * 2
def baseEnd_47417 : Nat := 2705301354927357163271

theorem tailTrace_47417 : CollatzResearch.WordTrace tailWord_47417 prefixEnd_47417 2705301354927357163271 := by
  unfold tailWord_47417
  simp only [CollatzResearch.WordTrace]
  refine ⟨1729440069223782023980505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1152960046149188015987003 1729440069223782023980505)
  ·
    refine ⟨1297080051917836517985379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1729440069223782023980505 1297080051917836517985379)
    ·
      refine ⟨1945620077876754776978069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1297080051917836517985379 1945620077876754776978069)
      ·
        refine ⟨91200941150472880170847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 1945620077876754776978069 91200941150472880170847)
        ·
          refine ⟨136801411725709320256271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91200941150472880170847 136801411725709320256271)
          ·
            refine ⟨205202117588563980384407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136801411725709320256271 205202117588563980384407)
            ·
              refine ⟨307803176382845970576611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205202117588563980384407 307803176382845970576611)
              ·
                refine ⟨461704764574268955864917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 307803176382845970576611 461704764574268955864917)
                ·
                  refine ⟨2705301354927357163271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 461704764574268955864917 2705301354927357163271)
                  ·
                    rfl

theorem cell23_47417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 9].length) (baseStart_47417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_47417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_47417 prefixEnd_47417 := by exact prefixLift 47417
  have htrace : WordTrace (prefixWord ++ tailWord_47417) baseStart_47417 baseEnd_47417 := by
    simpa [prefixWord, tailWord_47417, baseEnd_47417] using wordTrace_append hprefix tailTrace_47417
  have hstable : (prefixWord ++ tailWord_47417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47417).length < 2 ^ (prefixWord ++ tailWord_47417).sum := by decide
  have hdescent : baseEnd_47417 < baseStart_47417 := by decide
  rcases family_descends (prefixWord ++ tailWord_47417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47444 : List Nat := [2, 4, 1, 1, 2, 2, 1, 2, 2, 3, 3]
def baseStart_47444 : Nat := 118140960795 + 47444 * 2 ^ 59
def prefixEnd_47444 : Nat := 4983230072969 + 3 ^ 40 * 47444 * 2
def baseEnd_47444 : Nat := 24361576172017608831815

theorem tailTrace_47444 : CollatzResearch.WordTrace tailWord_47444 prefixEnd_47444 24361576172017608831815 := by
  unfold tailWord_47444
  simp only [CollatzResearch.WordTrace]
  refine ⟨865212420062982817606693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1153616560083977090142257 865212420062982817606693)
  ·
    refine ⟨162227328761809278301255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 865212420062982817606693 162227328761809278301255)
    ·
      refine ⟨243340993142713917451883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162227328761809278301255 243340993142713917451883)
      ·
        refine ⟨365011489714070876177825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243340993142713917451883 365011489714070876177825)
        ·
          refine ⟨273758617285553157133369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 365011489714070876177825 273758617285553157133369)
          ·
            refine ⟨205318962964164867850027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 273758617285553157133369 205318962964164867850027)
            ·
              refine ⟨307978444446247301775041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205318962964164867850027 307978444446247301775041)
              ·
                refine ⟨230983833334685476331281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 307978444446247301775041 230983833334685476331281)
                ·
                  refine ⟨173237875001014107248461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 230983833334685476331281 173237875001014107248461)
                  ·
                    refine ⟨64964203125380290218173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 173237875001014107248461 64964203125380290218173)
                    ·
                      refine ⟨24361576172017608831815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 64964203125380290218173 24361576172017608831815)
                      ·
                        rfl

theorem cell23_47444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_47444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_47444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_47444 prefixEnd_47444 := by exact prefixLift 47444
  have htrace : WordTrace (prefixWord ++ tailWord_47444) baseStart_47444 baseEnd_47444 := by
    simpa [prefixWord, tailWord_47444, baseEnd_47444] using wordTrace_append hprefix tailTrace_47444
  have hstable : (prefixWord ++ tailWord_47444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47444).length < 2 ^ (prefixWord ++ tailWord_47444).sum := by decide
  have hdescent : baseEnd_47444 < baseStart_47444 := by decide
  rcases family_descends (prefixWord ++ tailWord_47444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47445 : List Nat := [1, 3, 2, 2, 4, 2, 1, 2, 2, 2, 2]
def baseStart_47445 : Nat := 118140960795 + 47445 * 2 ^ 59
def prefixEnd_47445 : Nat := 4983230072969 + 3 ^ 40 * 47445 * 2
def baseEnd_47445 : Nat := 24362089652672104919311

theorem tailTrace_47445 : CollatzResearch.WordTrace tailWord_47445 prefixEnd_47445 24362089652672104919311 := by
  unfold tailWord_47445
  simp only [CollatzResearch.WordTrace]
  refine ⟨1730461313122342805999789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1153640875414895203999859 1730461313122342805999789)
  ·
    refine ⟨648922992420878552249921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1730461313122342805999789 648922992420878552249921)
    ·
      refine ⟨486692244315658914187441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 648922992420878552249921 486692244315658914187441)
      ·
        refine ⟨365019183236744185640581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 486692244315658914187441 365019183236744185640581)
        ·
          refine ⟨68441096856889534807609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 365019183236744185640581 68441096856889534807609)
          ·
            refine ⟨51330822642667151105707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68441096856889534807609 51330822642667151105707)
            ·
              refine ⟨76996233964000726658561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51330822642667151105707 76996233964000726658561)
              ·
                refine ⟨57747175473000544993921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76996233964000726658561 57747175473000544993921)
                ·
                  refine ⟨43310381604750408745441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57747175473000544993921 43310381604750408745441)
                  ·
                    refine ⟨32482786203562806559081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43310381604750408745441 32482786203562806559081)
                    ·
                      refine ⟨24362089652672104919311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 32482786203562806559081 24362089652672104919311)
                      ·
                        rfl

theorem cell23_47445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 2, 2, 2, 2].length) (baseStart_47445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_47445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_47445 prefixEnd_47445 := by exact prefixLift 47445
  have htrace : WordTrace (prefixWord ++ tailWord_47445) baseStart_47445 baseEnd_47445 := by
    simpa [prefixWord, tailWord_47445, baseEnd_47445] using wordTrace_append hprefix tailTrace_47445
  have hstable : (prefixWord ++ tailWord_47445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47445).length < 2 ^ (prefixWord ++ tailWord_47445).sum := by decide
  have hdescent : baseEnd_47445 < baseStart_47445 := by decide
  rcases family_descends (prefixWord ++ tailWord_47445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47447 : List Nat := [1, 1, 3, 2, 3, 1, 2, 1, 4, 5]
def baseStart_47447 : Nat := 118140960795 + 47447 * 2 ^ 59
def prefixEnd_47447 : Nat := 4983230072969 + 3 ^ 40 * 47447 * 2
def baseEnd_47447 : Nat := 8121038871327032364767

theorem tailTrace_47447 : CollatzResearch.WordTrace tailWord_47447 prefixEnd_47447 8121038871327032364767 := by
  unfold tailWord_47447
  simp only [CollatzResearch.WordTrace]
  refine ⟨1730534259115097147572595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1153689506076731431715063 1730534259115097147572595)
  ·
    refine ⟨2595801388672645721358893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1730534259115097147572595 2595801388672645721358893)
    ·
      refine ⟨973425520752242145509585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2595801388672645721358893 973425520752242145509585)
      ·
        refine ⟨730069140564181609132189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 973425520752242145509585 730069140564181609132189)
        ·
          refine ⟨273775927711568103424571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 730069140564181609132189 273775927711568103424571)
          ·
            refine ⟨410663891567352155136857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273775927711568103424571 410663891567352155136857)
            ·
              refine ⟨307997918675514116352643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 410663891567352155136857 307997918675514116352643)
              ·
                refine ⟨461996878013271174528965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 307997918675514116352643 461996878013271174528965)
                ·
                  refine ⟨86624414627488345224181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 461996878013271174528965 86624414627488345224181)
                  ·
                    refine ⟨8121038871327032364767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 86624414627488345224181 8121038871327032364767)
                    ·
                      rfl

theorem cell23_47447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 4, 5].length) (baseStart_47447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_47447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_47447 prefixEnd_47447 := by exact prefixLift 47447
  have htrace : WordTrace (prefixWord ++ tailWord_47447) baseStart_47447 baseEnd_47447 := by
    simpa [prefixWord, tailWord_47447, baseEnd_47447] using wordTrace_append hprefix tailTrace_47447
  have hstable : (prefixWord ++ tailWord_47447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47447).length < 2 ^ (prefixWord ++ tailWord_47447).sum := by decide
  have hdescent : baseEnd_47447 < baseStart_47447 := by decide
  rcases family_descends (prefixWord ++ tailWord_47447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47467 : List Nat := [1, 1, 1, 1, 2, 2, 2, 4, 4, 1, 4]
def baseStart_47467 : Nat := 118140960795 + 47467 * 2 ^ 59
def prefixEnd_47467 : Nat := 4983230072969 + 3 ^ 40 * 47467 * 2
def baseEnd_47467 : Nat := 24373386227071018844209

theorem tailTrace_47467 : CollatzResearch.WordTrace tailWord_47467 prefixEnd_47467 24373386227071018844209 := by
  unfold tailWord_47467
  simp only [CollatzResearch.WordTrace]
  refine ⟨1731263719042640563300655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1154175812695093708867103 1731263719042640563300655)
  ·
    refine ⟨2596895578563960844950983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1731263719042640563300655 2596895578563960844950983)
    ·
      refine ⟨3895343367845941267426475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2596895578563960844950983 3895343367845941267426475)
      ·
        refine ⟨5843015051768911901139713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3895343367845941267426475 5843015051768911901139713)
        ·
          refine ⟨4382261288826683925854785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5843015051768911901139713 4382261288826683925854785)
          ·
            refine ⟨3286695966620012944391089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4382261288826683925854785 3286695966620012944391089)
            ·
              refine ⟨2465021974965009708293317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3286695966620012944391089 2465021974965009708293317)
              ·
                refine ⟨462191620305939320304997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2465021974965009708293317 462191620305939320304997)
                ·
                  refine ⟨86660928807363622557187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 462191620305939320304997 86660928807363622557187)
                  ·
                    refine ⟨129991393211045433835781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 86660928807363622557187 129991393211045433835781)
                    ·
                      refine ⟨24373386227071018844209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 129991393211045433835781 24373386227071018844209)
                      ·
                        rfl

theorem cell23_47467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 4, 1, 4].length) (baseStart_47467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_47467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_47467 prefixEnd_47467 := by exact prefixLift 47467
  have htrace : WordTrace (prefixWord ++ tailWord_47467) baseStart_47467 baseEnd_47467 := by
    simpa [prefixWord, tailWord_47467, baseEnd_47467] using wordTrace_append hprefix tailTrace_47467
  have hstable : (prefixWord ++ tailWord_47467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47467).length < 2 ^ (prefixWord ++ tailWord_47467).sum := by decide
  have hdescent : baseEnd_47467 < baseStart_47467 := by decide
  rcases family_descends (prefixWord ++ tailWord_47467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47484 : List Nat := [2, 2, 2, 1, 1, 1, 2, 2, 4, 4, 2]
def baseStart_47484 : Nat := 118140960795 + 47484 * 2 ^ 59
def prefixEnd_47484 : Nat := 4983230072969 + 3 ^ 40 * 47484 * 2
def baseEnd_47484 : Nat := 24382115398197452331631

theorem tailTrace_47484 : CollatzResearch.WordTrace tailWord_47484 prefixEnd_47484 24382115398197452331631 := by
  unfold tailWord_47484
  simp only [CollatzResearch.WordTrace]
  refine ⟨865941879990526233334753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1154589173320701644446337 865941879990526233334753)
  ·
    refine ⟨649456409992894675001065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 865941879990526233334753 649456409992894675001065)
    ·
      refine ⟨487092307494671006250799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 649456409992894675001065 487092307494671006250799)
      ·
        refine ⟨730638461242006509376199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 487092307494671006250799 730638461242006509376199)
        ·
          refine ⟨1095957691863009764064299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 730638461242006509376199 1095957691863009764064299)
          ·
            refine ⟨1643936537794514646096449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1095957691863009764064299 1643936537794514646096449)
            ·
              refine ⟨1232952403345885984572337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1643936537794514646096449 1232952403345885984572337)
              ·
                refine ⟨924714302509414488429253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1232952403345885984572337 924714302509414488429253)
                ·
                  refine ⟨173383931720515216580485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 924714302509414488429253 173383931720515216580485)
                  ·
                    refine ⟨32509487197596603108841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 173383931720515216580485 32509487197596603108841)
                    ·
                      refine ⟨24382115398197452331631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 32509487197596603108841 24382115398197452331631)
                      ·
                        rfl

theorem cell23_47484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 4, 4, 2].length) (baseStart_47484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_47484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_47484 prefixEnd_47484 := by exact prefixLift 47484
  have htrace : WordTrace (prefixWord ++ tailWord_47484) baseStart_47484 baseEnd_47484 := by
    simpa [prefixWord, tailWord_47484, baseEnd_47484] using wordTrace_append hprefix tailTrace_47484
  have hstable : (prefixWord ++ tailWord_47484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47484).length < 2 ^ (prefixWord ++ tailWord_47484).sum := by decide
  have hdescent : baseEnd_47484 < baseStart_47484 := by decide
  rcases family_descends (prefixWord ++ tailWord_47484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47511 : List Nat := [1, 1, 3, 3, 1, 1, 2, 6, 1, 4]
def baseStart_47511 : Nat := 118140960795 + 47511 * 2 ^ 59
def prefixEnd_47511 : Nat := 4983230072969 + 3 ^ 40 * 47511 * 2
def baseEnd_47511 : Nat := 8131993125289615564669

theorem tailTrace_47511 : CollatzResearch.WordTrace tailWord_47511 prefixEnd_47511 8131993125289615564669 := by
  unfold tailWord_47511
  simp only [CollatzResearch.WordTrace]
  refine ⟨1732868530883236077902387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1155245687255490718601591 1732868530883236077902387)
  ·
    refine ⟨2599302796324854116853581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1732868530883236077902387 2599302796324854116853581)
    ·
      refine ⟨974738548621820293820093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2599302796324854116853581 974738548621820293820093)
      ·
        refine ⟨365526955733182610182535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 974738548621820293820093 365526955733182610182535)
        ·
          refine ⟨548290433599773915273803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365526955733182610182535 548290433599773915273803)
          ·
            refine ⟨822435650399660872910705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 548290433599773915273803 822435650399660872910705)
            ·
              refine ⟨616826737799745654683029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 822435650399660872910705 616826737799745654683029)
              ·
                refine ⟨28913753334363077563267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 616826737799745654683029 28913753334363077563267)
                ·
                  refine ⟨43370630001544616344901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28913753334363077563267 43370630001544616344901)
                  ·
                    refine ⟨8131993125289615564669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43370630001544616344901 8131993125289615564669)
                    ·
                      rfl

theorem cell23_47511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 6, 1, 4].length) (baseStart_47511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_47511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_47511 prefixEnd_47511 := by exact prefixLift 47511
  have htrace : WordTrace (prefixWord ++ tailWord_47511) baseStart_47511 baseEnd_47511 := by
    simpa [prefixWord, tailWord_47511, baseEnd_47511] using wordTrace_append hprefix tailTrace_47511
  have hstable : (prefixWord ++ tailWord_47511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47511).length < 2 ^ (prefixWord ++ tailWord_47511).sum := by decide
  have hdescent : baseEnd_47511 < baseStart_47511 := by decide
  rcases family_descends (prefixWord ++ tailWord_47511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47561 : List Nat := [1, 2, 1, 1, 2, 1, 6, 2, 2, 3, 2]
def baseStart_47561 : Nat := 118140960795 + 47561 * 2 ^ 59
def prefixEnd_47561 : Nat := 4983230072969 + 3 ^ 40 * 47561 * 2
def baseEnd_47561 : Nat := 24421653408593651068777

theorem tailTrace_47561 : CollatzResearch.WordTrace tailWord_47561 prefixEnd_47561 24421653408593651068777 := by
  unfold tailWord_47561
  simp only [CollatzResearch.WordTrace]
  refine ⟨1734692180702094617222537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1156461453801396411481691 1734692180702094617222537)
  ·
    refine ⟨1301019135526570962916903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1734692180702094617222537 1301019135526570962916903)
    ·
      refine ⟨1951528703289856444375355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1301019135526570962916903 1951528703289856444375355)
      ·
        refine ⟨2927293054934784666563033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1951528703289856444375355 2927293054934784666563033)
        ·
          refine ⟨2195469791201088499922275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2927293054934784666563033 2195469791201088499922275)
          ·
            refine ⟨3293204686801632749883413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2195469791201088499922275 3293204686801632749883413)
            ·
              refine ⟨154368969693826535150785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3293204686801632749883413 154368969693826535150785)
              ·
                refine ⟨115776727270369901363089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154368969693826535150785 115776727270369901363089)
                ·
                  refine ⟨86832545452777426022317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115776727270369901363089 86832545452777426022317)
                  ·
                    refine ⟨32562204544791534758369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 86832545452777426022317 32562204544791534758369)
                    ·
                      refine ⟨24421653408593651068777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 32562204544791534758369 24421653408593651068777)
                      ·
                        rfl

theorem cell23_47561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 2, 2, 3, 2].length) (baseStart_47561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_47561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_47561 prefixEnd_47561 := by exact prefixLift 47561
  have htrace : WordTrace (prefixWord ++ tailWord_47561) baseStart_47561 baseEnd_47561 := by
    simpa [prefixWord, tailWord_47561, baseEnd_47561] using wordTrace_append hprefix tailTrace_47561
  have hstable : (prefixWord ++ tailWord_47561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47561).length < 2 ^ (prefixWord ++ tailWord_47561).sum := by decide
  have hdescent : baseEnd_47561 < baseStart_47561 := by decide
  rcases family_descends (prefixWord ++ tailWord_47561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47567 : List Nat := [1, 1, 2, 1, 1, 4, 1, 1, 5, 6]
def baseStart_47567 : Nat := 118140960795 + 47567 * 2 ^ 59
def prefixEnd_47567 : Nat := 4983230072969 + 3 ^ 40 * 47567 * 2
def baseEnd_47567 : Nat := 8141578097506875864583

theorem tailTrace_47567 : CollatzResearch.WordTrace tailWord_47567 prefixEnd_47567 8141578097506875864583 := by
  unfold tailWord_47567
  simp only [CollatzResearch.WordTrace]
  refine ⟨1734911018680357641940955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1156607345786905094627303 1734911018680357641940955)
  ·
    refine ⟨2602366528020536462911433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1734911018680357641940955 2602366528020536462911433)
    ·
      refine ⟨1951774896015402347183575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2602366528020536462911433 1951774896015402347183575)
      ·
        refine ⟨2927662344023103520775363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1951774896015402347183575 2927662344023103520775363)
        ·
          refine ⟨4391493516034655281163045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2927662344023103520775363 4391493516034655281163045)
          ·
            refine ⟨823405034256497865218071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4391493516034655281163045 823405034256497865218071)
            ·
              refine ⟨1235107551384746797827107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 823405034256497865218071 1235107551384746797827107)
              ·
                refine ⟨1852661327077120196740661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1235107551384746797827107 1852661327077120196740661)
                ·
                  refine ⟨173686999413480018444437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1852661327077120196740661 173686999413480018444437)
                  ·
                    refine ⟨8141578097506875864583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 173686999413480018444437 8141578097506875864583)
                    ·
                      rfl

theorem cell23_47567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 5, 6].length) (baseStart_47567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_47567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_47567 prefixEnd_47567 := by exact prefixLift 47567
  have htrace : WordTrace (prefixWord ++ tailWord_47567) baseStart_47567 baseEnd_47567 := by
    simpa [prefixWord, tailWord_47567, baseEnd_47567] using wordTrace_append hprefix tailTrace_47567
  have hstable : (prefixWord ++ tailWord_47567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47567).length < 2 ^ (prefixWord ++ tailWord_47567).sum := by decide
  have hdescent : baseEnd_47567 < baseStart_47567 := by decide
  rcases family_descends (prefixWord ++ tailWord_47567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47584 : List Nat := [2, 1, 1, 3, 1, 1, 6, 1, 1, 6]
def baseStart_47584 : Nat := 118140960795 + 47584 * 2 ^ 59
def prefixEnd_47584 : Nat := 4983230072969 + 3 ^ 40 * 47584 * 2
def baseEnd_47584 : Nat := 8144487821215687027057

theorem tailTrace_47584 : CollatzResearch.WordTrace tailWord_47584 prefixEnd_47584 8144487821215687027057 := by
  unfold tailWord_47584
  simp only [CollatzResearch.WordTrace]
  refine ⟨867765529809384772654903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1157020706412513030206537 867765529809384772654903)
  ·
    refine ⟨1301648294714077158982355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 867765529809384772654903 1301648294714077158982355)
    ·
      refine ⟨1952472442071115738473533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1301648294714077158982355 1952472442071115738473533)
      ·
        refine ⟨732177165776668401927575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1952472442071115738473533 732177165776668401927575)
        ·
          refine ⟨1098265748665002602891363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 732177165776668401927575 1098265748665002602891363)
          ·
            refine ⟨1647398622997503904337045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1098265748665002602891363 1647398622997503904337045)
            ·
              refine ⟨77221810453007995515799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1647398622997503904337045 77221810453007995515799)
              ·
                refine ⟨115832715679511993273699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77221810453007995515799 115832715679511993273699)
                ·
                  refine ⟨173749073519267989910549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115832715679511993273699 173749073519267989910549)
                  ·
                    refine ⟨8144487821215687027057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 173749073519267989910549 8144487821215687027057)
                    ·
                      rfl

theorem cell23_47584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 1, 1, 6].length) (baseStart_47584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_47584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_47584 prefixEnd_47584 := by exact prefixLift 47584
  have htrace : WordTrace (prefixWord ++ tailWord_47584) baseStart_47584 baseEnd_47584 := by
    simpa [prefixWord, tailWord_47584, baseEnd_47584] using wordTrace_append hprefix tailTrace_47584
  have hstable : (prefixWord ++ tailWord_47584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47584).length < 2 ^ (prefixWord ++ tailWord_47584).sum := by decide
  have hdescent : baseEnd_47584 < baseStart_47584 := by decide
  rcases family_descends (prefixWord ++ tailWord_47584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47591 : List Nat := [1, 1, 5, 2, 1, 1, 2, 4, 1, 1, 4]
def baseStart_47591 : Nat := 118140960795 + 47591 * 2 ^ 59
def prefixEnd_47591 : Nat := 4983230072969 + 3 ^ 40 * 47591 * 2
def baseEnd_47591 : Nat := 24437057828228533693639

theorem tailTrace_47591 : CollatzResearch.WordTrace tailWord_47591 prefixEnd_47591 24437057828228533693639 := by
  unfold tailWord_47591
  simp only [CollatzResearch.WordTrace]
  refine ⟨1735786370593409740814627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1157190913728939827209751 1735786370593409740814627)
  ·
    refine ⟨2603679555890114611221941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1735786370593409740814627 2603679555890114611221941)
    ·
      refine ⟨244094958364698244802057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2603679555890114611221941 244094958364698244802057)
      ·
        refine ⟨183071218773523683601543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244094958364698244802057 183071218773523683601543)
        ·
          refine ⟨274606828160285525402315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183071218773523683601543 274606828160285525402315)
          ·
            refine ⟨411910242240428288103473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274606828160285525402315 411910242240428288103473)
            ·
              refine ⟨308932681680321216077605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 411910242240428288103473 308932681680321216077605)
              ·
                refine ⟨57924877815060228014551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 308932681680321216077605 57924877815060228014551)
                ·
                  refine ⟨86887316722590342021827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57924877815060228014551 86887316722590342021827)
                  ·
                    refine ⟨130330975083885513032741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 86887316722590342021827 130330975083885513032741)
                    ·
                      refine ⟨24437057828228533693639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 130330975083885513032741 24437057828228533693639)
                      ·
                        rfl

theorem cell23_47591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_47591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_47591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_47591 prefixEnd_47591 := by exact prefixLift 47591
  have htrace : WordTrace (prefixWord ++ tailWord_47591) baseStart_47591 baseEnd_47591 := by
    simpa [prefixWord, tailWord_47591, baseEnd_47591] using wordTrace_append hprefix tailTrace_47591
  have hstable : (prefixWord ++ tailWord_47591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47591).length < 2 ^ (prefixWord ++ tailWord_47591).sum := by decide
  have hdescent : baseEnd_47591 < baseStart_47591 := by decide
  rcases family_descends (prefixWord ++ tailWord_47591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47602 : List Nat := [3, 2, 1, 4, 2, 1, 2, 3, 1, 1, 3]
def baseStart_47602 : Nat := 118140960795 + 47602 * 2 ^ 59
def prefixEnd_47602 : Nat := 4983230072969 + 3 ^ 40 * 47602 * 2
def baseEnd_47602 : Nat := 24442706115427990656089

theorem tailTrace_47602 : CollatzResearch.WordTrace tailWord_47602 prefixEnd_47602 24442706115427990656089 := by
  unfold tailWord_47602
  simp only [CollatzResearch.WordTrace]
  refine ⟨434046893388389654866265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1157458382369039079643373 434046893388389654866265)
  ·
    refine ⟨325535170041292241149699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 434046893388389654866265 325535170041292241149699)
    ·
      refine ⟨488302755061938361724549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325535170041292241149699 488302755061938361724549)
      ·
        refine ⟨91556766574113442823353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 488302755061938361724549 91556766574113442823353)
        ·
          refine ⟨68667574930585082117515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91556766574113442823353 68667574930585082117515)
          ·
            refine ⟨103001362395877623176273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68667574930585082117515 103001362395877623176273)
            ·
              refine ⟨77251021796908217382205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103001362395877623176273 77251021796908217382205)
              ·
                refine ⟨28969133173840581518327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77251021796908217382205 28969133173840581518327)
                ·
                  refine ⟨43453699760760872277491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28969133173840581518327 43453699760760872277491)
                  ·
                    refine ⟨65180549641141308416237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43453699760760872277491 65180549641141308416237)
                    ·
                      refine ⟨24442706115427990656089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 65180549641141308416237 24442706115427990656089)
                      ·
                        rfl

theorem cell23_47602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_47602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_47602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_47602 prefixEnd_47602 := by exact prefixLift 47602
  have htrace : WordTrace (prefixWord ++ tailWord_47602) baseStart_47602 baseEnd_47602 := by
    simpa [prefixWord, tailWord_47602, baseEnd_47602] using wordTrace_append hprefix tailTrace_47602
  have hstable : (prefixWord ++ tailWord_47602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47602).length < 2 ^ (prefixWord ++ tailWord_47602).sum := by decide
  have hdescent : baseEnd_47602 < baseStart_47602 := by decide
  rcases family_descends (prefixWord ++ tailWord_47602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47607 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 7]
def baseStart_47607 : Nat := 118140960795 + 47607 * 2 ^ 59
def prefixEnd_47607 : Nat := 4983230072969 + 3 ^ 40 * 47607 * 2
def baseEnd_47607 : Nat := 24445273518700471093565

theorem tailTrace_47607 : CollatzResearch.WordTrace tailWord_47607 prefixEnd_47607 24445273518700471093565 := by
  unfold tailWord_47607
  simp only [CollatzResearch.WordTrace]
  refine ⟨1736369938535444473397075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1157579959023629648931383 1736369938535444473397075)
  ·
    refine ⟨2604554907803166710095613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1736369938535444473397075 2604554907803166710095613)
    ·
      refine ⟨976708090426187516285855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2604554907803166710095613 976708090426187516285855)
      ·
        refine ⟨1465062135639281274428783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 976708090426187516285855 1465062135639281274428783)
        ·
          refine ⟨2197593203458921911643175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1465062135639281274428783 2197593203458921911643175)
          ·
            refine ⟨3296389805188382867464763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2197593203458921911643175 3296389805188382867464763)
            ·
              refine ⟨4944584707782574301197145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3296389805188382867464763 4944584707782574301197145)
              ·
                refine ⟨3708438530836930725897859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4944584707782574301197145 3708438530836930725897859)
                ·
                  refine ⟨5562657796255396088846789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3708438530836930725897859 5562657796255396088846789)
                  ·
                    refine ⟨1042998336797886766658773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5562657796255396088846789 1042998336797886766658773)
                    ·
                      refine ⟨24445273518700471093565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 1042998336797886766658773 24445273518700471093565)
                      ·
                        rfl

theorem cell23_47607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 7].length) (baseStart_47607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_47607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_47607 prefixEnd_47607 := by exact prefixLift 47607
  have htrace : WordTrace (prefixWord ++ tailWord_47607) baseStart_47607 baseEnd_47607 := by
    simpa [prefixWord, tailWord_47607, baseEnd_47607] using wordTrace_append hprefix tailTrace_47607
  have hstable : (prefixWord ++ tailWord_47607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47607).length < 2 ^ (prefixWord ++ tailWord_47607).sum := by decide
  have hdescent : baseEnd_47607 < baseStart_47607 := by decide
  rcases family_descends (prefixWord ++ tailWord_47607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47648 : List Nat := [2, 1, 1, 6, 2, 2, 2, 7]
def baseStart_47648 : Nat := 118140960795 + 47648 * 2 ^ 59
def prefixEnd_47648 : Nat := 4983230072969 + 3 ^ 40 * 47648 * 2
def baseEnd_47648 : Nat := 906160230575363358551

theorem tailTrace_47648 : CollatzResearch.WordTrace tailWord_47648 prefixEnd_47648 906160230575363358551 := by
  unfold tailWord_47648
  simp only [CollatzResearch.WordTrace]
  refine ⟨868932665693454237819799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1158576887591272317093065 868932665693454237819799)
  ·
    refine ⟨1303398998540181356729699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 868932665693454237819799 1303398998540181356729699)
    ·
      refine ⟨1955098497810272035094549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1303398998540181356729699 1955098497810272035094549)
      ·
        refine ⟨91645242084856501645057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 1955098497810272035094549 91645242084856501645057)
        ·
          refine ⟨68733931563642376233793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91645242084856501645057 68733931563642376233793)
          ·
            refine ⟨51550448672731782175345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68733931563642376233793 51550448672731782175345)
            ·
              refine ⟨38662836504548836631509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51550448672731782175345 38662836504548836631509)
              ·
                refine ⟨906160230575363358551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 38662836504548836631509 906160230575363358551)
                ·
                  rfl

theorem cell23_47648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 2, 7].length) (baseStart_47648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_47648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_47648 prefixEnd_47648 := by exact prefixLift 47648
  have htrace : WordTrace (prefixWord ++ tailWord_47648) baseStart_47648 baseEnd_47648 := by
    simpa [prefixWord, tailWord_47648, baseEnd_47648] using wordTrace_append hprefix tailTrace_47648
  have hstable : (prefixWord ++ tailWord_47648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47648).length < 2 ^ (prefixWord ++ tailWord_47648).sum := by decide
  have hdescent : baseEnd_47648 < baseStart_47648 := by decide
  rcases family_descends (prefixWord ++ tailWord_47648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47658 : List Nat := [3, 1, 4, 1, 1, 2, 1, 2, 4, 1, 3]
def baseStart_47658 : Nat := 118140960795 + 47658 * 2 ^ 59
def prefixEnd_47658 : Nat := 4983230072969 + 3 ^ 40 * 47658 * 2
def baseEnd_47658 : Nat := 24471461032079771555831

theorem tailTrace_47658 : CollatzResearch.WordTrace tailWord_47658 prefixEnd_47658 24471461032079771555831 := by
  unfold tailWord_47658
  simp only [CollatzResearch.WordTrace]
  refine ⟨434557515337670045875907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1158820040900453455669085 434557515337670045875907)
  ·
    refine ⟨651836273006505068813861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 434557515337670045875907 651836273006505068813861)
    ·
      refine ⟨122219301188719700402599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 651836273006505068813861 122219301188719700402599)
      ·
        refine ⟨183328951783079550603899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122219301188719700402599 183328951783079550603899)
        ·
          refine ⟨274993427674619325905849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183328951783079550603899 274993427674619325905849)
          ·
            refine ⟨206245070755964494429387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 274993427674619325905849 206245070755964494429387)
            ·
              refine ⟨309367606133946741644081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206245070755964494429387 309367606133946741644081)
              ·
                refine ⟨232025704600460056233061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 309367606133946741644081 232025704600460056233061)
                ·
                  refine ⟨43504819612586260543699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 232025704600460056233061 43504819612586260543699)
                  ·
                    refine ⟨65257229418879390815549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43504819612586260543699 65257229418879390815549)
                    ·
                      refine ⟨24471461032079771555831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 65257229418879390815549 24471461032079771555831)
                      ·
                        rfl

theorem cell23_47658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_47658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_47658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_47658 prefixEnd_47658 := by exact prefixLift 47658
  have htrace : WordTrace (prefixWord ++ tailWord_47658) baseStart_47658 baseEnd_47658 := by
    simpa [prefixWord, tailWord_47658, baseEnd_47658] using wordTrace_append hprefix tailTrace_47658
  have hstable : (prefixWord ++ tailWord_47658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47658).length < 2 ^ (prefixWord ++ tailWord_47658).sum := by decide
  have hdescent : baseEnd_47658 < baseStart_47658 := by decide
  rcases family_descends (prefixWord ++ tailWord_47658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47698 : List Nat := [3, 2, 2, 1, 2, 1, 2, 3, 1, 4, 2]
def baseStart_47698 : Nat := 118140960795 + 47698 * 2 ^ 59
def prefixEnd_47698 : Nat := 4983230072969 + 3 ^ 40 * 47698 * 2
def baseEnd_47698 : Nat := 24492000258259615055647

theorem tailTrace_47698 : CollatzResearch.WordTrace tailWord_47698 prefixEnd_47698 24492000258259615055647 := by
  unfold tailWord_47698
  simp only [CollatzResearch.WordTrace]
  refine ⟨434922245301441753739937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1159792654137178009973165 434922245301441753739937)
  ·
    refine ⟨326191683976081315304953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 434922245301441753739937 326191683976081315304953)
    ·
      refine ⟨244643762982060986478715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326191683976081315304953 244643762982060986478715)
      ·
        refine ⟨366965644473091479718073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244643762982060986478715 366965644473091479718073)
        ·
          refine ⟨275224233354818609788555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 366965644473091479718073 275224233354818609788555)
          ·
            refine ⟨412836350032227914682833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275224233354818609788555 412836350032227914682833)
            ·
              refine ⟨309627262524170936012125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 412836350032227914682833 309627262524170936012125)
              ·
                refine ⟨116110223446564101004547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 309627262524170936012125 116110223446564101004547)
                ·
                  refine ⟨174165335169846151506821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116110223446564101004547 174165335169846151506821)
                  ·
                    refine ⟨32656000344346153407529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 174165335169846151506821 32656000344346153407529)
                    ·
                      refine ⟨24492000258259615055647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 32656000344346153407529 24492000258259615055647)
                      ·
                        rfl

theorem cell23_47698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 3, 1, 4, 2].length) (baseStart_47698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_47698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_47698 prefixEnd_47698 := by exact prefixLift 47698
  have htrace : WordTrace (prefixWord ++ tailWord_47698) baseStart_47698 baseEnd_47698 := by
    simpa [prefixWord, tailWord_47698, baseEnd_47698] using wordTrace_append hprefix tailTrace_47698
  have hstable : (prefixWord ++ tailWord_47698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47698).length < 2 ^ (prefixWord ++ tailWord_47698).sum := by decide
  have hdescent : baseEnd_47698 < baseStart_47698 := by decide
  rcases family_descends (prefixWord ++ tailWord_47698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47704 : List Nat := [2, 1, 2, 2, 1, 2, 2, 4, 7]
def baseStart_47704 : Nat := 118140960795 + 47704 * 2 ^ 59
def prefixEnd_47704 : Nat := 4983230072969 + 3 ^ 40 * 47704 * 2
def baseEnd_47704 : Nat := 2721675682465176842291

theorem tailTrace_47704 : CollatzResearch.WordTrace tailWord_47704 prefixEnd_47704 2721675682465176842291 := by
  unfold tailWord_47704
  simp only [CollatzResearch.WordTrace]
  refine ⟨869953909592015019839083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1159938546122686693118777 869953909592015019839083)
  ·
    refine ⟨1304930864388022529758625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 869953909592015019839083 1304930864388022529758625)
    ·
      refine ⟨978698148291016897318969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1304930864388022529758625 978698148291016897318969)
      ·
        refine ⟨734023611218262672989227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 978698148291016897318969 734023611218262672989227)
        ·
          refine ⟨1101035416827394009483841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 734023611218262672989227 1101035416827394009483841)
          ·
            refine ⟨825776562620545507112881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1101035416827394009483841 825776562620545507112881)
            ·
              refine ⟨619332421965409130334661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 825776562620545507112881 619332421965409130334661)
              ·
                refine ⟨116124829118514211937749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 619332421965409130334661 116124829118514211937749)
                ·
                  refine ⟨2721675682465176842291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 116124829118514211937749 2721675682465176842291)
                  ·
                    rfl

theorem cell23_47704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 4, 7].length) (baseStart_47704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_47704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_47704 prefixEnd_47704 := by exact prefixLift 47704
  have htrace : WordTrace (prefixWord ++ tailWord_47704) baseStart_47704 baseEnd_47704 := by
    simpa [prefixWord, tailWord_47704, baseEnd_47704] using wordTrace_append hprefix tailTrace_47704
  have hstable : (prefixWord ++ tailWord_47704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47704).length < 2 ^ (prefixWord ++ tailWord_47704).sum := by decide
  have hdescent : baseEnd_47704 < baseStart_47704 := by decide
  rcases family_descends (prefixWord ++ tailWord_47704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47721 : List Nat := [1, 2, 1, 1, 1, 4, 1, 7, 5]
def baseStart_47721 : Nat := 118140960795 + 47721 * 2 ^ 59
def prefixEnd_47721 : Nat := 4983230072969 + 3 ^ 40 * 47721 * 2
def baseEnd_47721 : Nat := 2722645590368113896449

theorem tailTrace_47721 : CollatzResearch.WordTrace tailWord_47721 prefixEnd_47721 2722645590368113896449 := by
  unfold tailWord_47721
  simp only [CollatzResearch.WordTrace]
  refine ⟨1740527860122441943047017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1160351906748294628698011 1740527860122441943047017)
  ·
    refine ⟨1305395895091831457285263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1740527860122441943047017 1305395895091831457285263)
    ·
      refine ⟨1958093842637747185927895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1305395895091831457285263 1958093842637747185927895)
      ·
        refine ⟨2937140763956620778891843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1958093842637747185927895 2937140763956620778891843)
        ·
          refine ⟨4405711145934931168337765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2937140763956620778891843 4405711145934931168337765)
          ·
            refine ⟨826070839862799594063331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4405711145934931168337765 826070839862799594063331)
            ·
              refine ⟨1239106259794199391094997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 826070839862799594063331 1239106259794199391094997)
              ·
                refine ⟨29041552963926548228789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1239106259794199391094997 29041552963926548228789)
                ·
                  refine ⟨2722645590368113896449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29041552963926548228789 2722645590368113896449)
                  ·
                    rfl

theorem cell23_47721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 7, 5].length) (baseStart_47721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_47721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_47721 prefixEnd_47721 := by exact prefixLift 47721
  have htrace : WordTrace (prefixWord ++ tailWord_47721) baseStart_47721 baseEnd_47721 := by
    simpa [prefixWord, tailWord_47721, baseEnd_47721] using wordTrace_append hprefix tailTrace_47721
  have hstable : (prefixWord ++ tailWord_47721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47721).length < 2 ^ (prefixWord ++ tailWord_47721).sum := by decide
  have hdescent : baseEnd_47721 < baseStart_47721 := by decide
  rcases family_descends (prefixWord ++ tailWord_47721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47748 : List Nat := [2, 3, 2, 1, 3, 2, 1, 1, 2, 3, 3]
def baseStart_47748 : Nat := 118140960795 + 47748 * 2 ^ 59
def prefixEnd_47748 : Nat := 4983230072969 + 3 ^ 40 * 47748 * 2
def baseEnd_47748 : Nat := 24517674290984419430417

theorem tailTrace_47748 : CollatzResearch.WordTrace tailWord_47748 prefixEnd_47748 24517674290984419430417 := by
  unfold tailWord_47748
  simp only [CollatzResearch.WordTrace]
  refine ⟨870756315512312777139949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1161008420683083702853265 870756315512312777139949)
  ·
    refine ⟨326533618317117291427481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 870756315512312777139949 326533618317117291427481)
    ·
      refine ⟨244900213737837968570611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326533618317117291427481 244900213737837968570611)
      ·
        refine ⟨367350320606756952855917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244900213737837968570611 367350320606756952855917)
        ·
          refine ⟨137756370227533857320969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 367350320606756952855917 137756370227533857320969)
          ·
            refine ⟨103317277670650392990727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137756370227533857320969 103317277670650392990727)
            ·
              refine ⟨154975916505975589486091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103317277670650392990727 154975916505975589486091)
              ·
                refine ⟨232463874758963384229137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154975916505975589486091 232463874758963384229137)
                ·
                  refine ⟨174347906069222538171853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 232463874758963384229137 174347906069222538171853)
                  ·
                    refine ⟨65380464775958451814445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 174347906069222538171853 65380464775958451814445)
                    ·
                      refine ⟨24517674290984419430417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 65380464775958451814445 24517674290984419430417)
                      ·
                        rfl

theorem cell23_47748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_47748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_47748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_47748 prefixEnd_47748 := by exact prefixLift 47748
  have htrace : WordTrace (prefixWord ++ tailWord_47748) baseStart_47748 baseEnd_47748 := by
    simpa [prefixWord, tailWord_47748, baseEnd_47748] using wordTrace_append hprefix tailTrace_47748
  have hstable : (prefixWord ++ tailWord_47748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47748).length < 2 ^ (prefixWord ++ tailWord_47748).sum := by decide
  have hdescent : baseEnd_47748 < baseStart_47748 := by decide
  rcases family_descends (prefixWord ++ tailWord_47748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47758 : List Nat := [4, 1, 1, 3, 1, 1, 1, 2, 2, 5, 2]
def baseStart_47758 : Nat := 118140960795 + 47758 * 2 ^ 59
def prefixEnd_47758 : Nat := 4983230072969 + 3 ^ 40 * 47758 * 2
def baseEnd_47758 : Nat := 24522809097529380305371

theorem tailTrace_47758 : CollatzResearch.WordTrace tailWord_47758 prefixEnd_47758 24522809097529380305371 := by
  unfold tailWord_47758
  simp only [CollatzResearch.WordTrace]
  refine ⟨217734670123549657767991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1161251573992264841429285 217734670123549657767991)
  ·
    refine ⟨326602005185324486651987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217734670123549657767991 326602005185324486651987)
    ·
      refine ⟨489903007777986729977981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326602005185324486651987 489903007777986729977981)
      ·
        refine ⟨183713627916745023741743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 489903007777986729977981 183713627916745023741743)
        ·
          refine ⟨275570441875117535612615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183713627916745023741743 275570441875117535612615)
          ·
            refine ⟨413355662812676303418923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275570441875117535612615 413355662812676303418923)
            ·
              refine ⟨620033494219014455128385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 413355662812676303418923 620033494219014455128385)
              ·
                refine ⟨465025120664260841346289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 620033494219014455128385 465025120664260841346289)
                ·
                  refine ⟨348768840498195631009717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 465025120664260841346289 348768840498195631009717)
                  ·
                    refine ⟨32697078796705840407161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 348768840498195631009717 32697078796705840407161)
                    ·
                      refine ⟨24522809097529380305371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 32697078796705840407161 24522809097529380305371)
                      ·
                        rfl

theorem cell23_47758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_47758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_47758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_47758 prefixEnd_47758 := by exact prefixLift 47758
  have htrace : WordTrace (prefixWord ++ tailWord_47758) baseStart_47758 baseEnd_47758 := by
    simpa [prefixWord, tailWord_47758, baseEnd_47758] using wordTrace_append hprefix tailTrace_47758
  have hstable : (prefixWord ++ tailWord_47758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47758).length < 2 ^ (prefixWord ++ tailWord_47758).sum := by decide
  have hdescent : baseEnd_47758 < baseStart_47758 := by decide
  rcases family_descends (prefixWord ++ tailWord_47758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47781 : List Nat := [1, 3, 1, 2, 1, 2, 1, 1, 7, 4]
def baseStart_47781 : Nat := 118140960795 + 47781 * 2 ^ 59
def prefixEnd_47781 : Nat := 4983230072969 + 3 ^ 40 * 47781 * 2
def baseEnd_47781 : Nat := 8178206384194263439255

theorem tailTrace_47781 : CollatzResearch.WordTrace tailWord_47781 prefixEnd_47781 8178206384194263439255 := by
  unfold tailWord_47781
  simp only [CollatzResearch.WordTrace]
  refine ⟨1742716239905072190231197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1161810826603381460154131 1742716239905072190231197)
  ·
    refine ⟨653518589964402071336699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1742716239905072190231197 653518589964402071336699)
    ·
      refine ⟨980277884946603107005049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 653518589964402071336699 980277884946603107005049)
      ·
        refine ⟨735208413709952330253787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 980277884946603107005049 735208413709952330253787)
        ·
          refine ⟨1102812620564928495380681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 735208413709952330253787 1102812620564928495380681)
          ·
            refine ⟨827109465423696371535511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1102812620564928495380681 827109465423696371535511)
            ·
              refine ⟨1240664198135544557303267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 827109465423696371535511 1240664198135544557303267)
              ·
                refine ⟨1860996297203316835954901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1240664198135544557303267 1860996297203316835954901)
                ·
                  refine ⟨43617100715702738342693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1860996297203316835954901 43617100715702738342693)
                  ·
                    refine ⟨8178206384194263439255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43617100715702738342693 8178206384194263439255)
                    ·
                      rfl

theorem cell23_47781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 7, 4].length) (baseStart_47781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_47781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_47781 prefixEnd_47781 := by exact prefixLift 47781
  have htrace : WordTrace (prefixWord ++ tailWord_47781) baseStart_47781 baseEnd_47781 := by
    simpa [prefixWord, tailWord_47781, baseEnd_47781] using wordTrace_append hprefix tailTrace_47781
  have hstable : (prefixWord ++ tailWord_47781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47781).length < 2 ^ (prefixWord ++ tailWord_47781).sum := by decide
  have hdescent : baseEnd_47781 < baseStart_47781 := by decide
  rcases family_descends (prefixWord ++ tailWord_47781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47832 : List Nat := [2, 1, 2, 2, 3, 4, 1, 3, 1, 4]
def baseStart_47832 : Nat := 118140960795 + 47832 * 2 ^ 59
def prefixEnd_47832 : Nat := 4983230072969 + 3 ^ 40 * 47832 * 2
def baseEnd_47832 : Nat := 8186935555320696926677

theorem tailTrace_47832 : CollatzResearch.WordTrace tailWord_47832 prefixEnd_47832 8186935555320696926677 := by
  unfold tailWord_47832
  simp only [CollatzResearch.WordTrace]
  refine ⟨872288181360153950168875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1163050908480205266891833 872288181360153950168875)
  ·
    refine ⟨1308432272040230925253313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 872288181360153950168875 1308432272040230925253313)
    ·
      refine ⟨981324204030173193939985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1308432272040230925253313 981324204030173193939985)
      ·
        refine ⟨735993153022629895454989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 981324204030173193939985 735993153022629895454989)
        ·
          refine ⟨275997432383486210795621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 735993153022629895454989 275997432383486210795621)
          ·
            refine ⟨51749518571903664524179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 275997432383486210795621 51749518571903664524179)
            ·
              refine ⟨77624277857855496786269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51749518571903664524179 77624277857855496786269)
              ·
                refine ⟨29109104196695811294851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77624277857855496786269 29109104196695811294851)
                ·
                  refine ⟨43663656295043716942277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29109104196695811294851 43663656295043716942277)
                  ·
                    refine ⟨8186935555320696926677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43663656295043716942277 8186935555320696926677)
                    ·
                      rfl

theorem cell23_47832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 3, 1, 4].length) (baseStart_47832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_47832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_47832 prefixEnd_47832 := by exact prefixLift 47832
  have htrace : WordTrace (prefixWord ++ tailWord_47832) baseStart_47832 baseEnd_47832 := by
    simpa [prefixWord, tailWord_47832, baseEnd_47832] using wordTrace_append hprefix tailTrace_47832
  have hstable : (prefixWord ++ tailWord_47832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47832).length < 2 ^ (prefixWord ++ tailWord_47832).sum := by decide
  have hdescent : baseEnd_47832 < baseStart_47832 := by decide
  rcases family_descends (prefixWord ++ tailWord_47832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47855 : List Nat := [1, 1, 2, 1, 5, 2, 3, 1, 3, 1, 3]
def baseStart_47855 : Nat := 118140960795 + 47855 * 2 ^ 59
def prefixEnd_47855 : Nat := 4983230072969 + 3 ^ 40 * 47855 * 2
def baseEnd_47855 : Nat := 24572616721015500792425

theorem tailTrace_47855 : CollatzResearch.WordTrace tailWord_47855 prefixEnd_47855 24572616721015500792425 := by
  unfold tailWord_47855
  simp only [CollatzResearch.WordTrace]
  refine ⟨1745415241636982828425019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1163610161091321885616679 1745415241636982828425019)
  ·
    refine ⟨2618122862455474242637529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1745415241636982828425019 2618122862455474242637529)
    ·
      refine ⟨1963592146841605681978147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2618122862455474242637529 1963592146841605681978147)
      ·
        refine ⟨2945388220262408522967221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1963592146841605681978147 2945388220262408522967221)
        ·
          refine ⟨276130145649600799028177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2945388220262408522967221 276130145649600799028177)
          ·
            refine ⟨207097609237200599271133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 276130145649600799028177 207097609237200599271133)
            ·
              refine ⟨77661603463950224726675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 207097609237200599271133 77661603463950224726675)
              ·
                refine ⟨116492405195925337090013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77661603463950224726675 116492405195925337090013)
                ·
                  refine ⟨43684651948472001408755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 116492405195925337090013 43684651948472001408755)
                  ·
                    refine ⟨65526977922708002113133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43684651948472001408755 65526977922708002113133)
                    ·
                      refine ⟨24572616721015500792425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 65526977922708002113133 24572616721015500792425)
                      ·
                        rfl

theorem cell23_47855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 1, 3, 1, 3].length) (baseStart_47855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_47855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_47855 prefixEnd_47855 := by exact prefixLift 47855
  have htrace : WordTrace (prefixWord ++ tailWord_47855) baseStart_47855 baseEnd_47855 := by
    simpa [prefixWord, tailWord_47855, baseEnd_47855] using wordTrace_append hprefix tailTrace_47855
  have hstable : (prefixWord ++ tailWord_47855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47855).length < 2 ^ (prefixWord ++ tailWord_47855).sum := by decide
  have hdescent : baseEnd_47855 < baseStart_47855 := by decide
  rcases family_descends (prefixWord ++ tailWord_47855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47871 : List Nat := [1, 1, 2, 2, 1, 3, 1, 5, 1, 6]
def baseStart_47871 : Nat := 118140960795 + 47871 * 2 ^ 59
def prefixEnd_47871 : Nat := 4983230072969 + 3 ^ 40 * 47871 * 2
def baseEnd_47871 : Nat := 8193610803829146064117

theorem tailTrace_47871 : CollatzResearch.WordTrace tailWord_47871 prefixEnd_47871 8193610803829146064117 := by
  unfold tailWord_47871
  simp only [CollatzResearch.WordTrace]
  refine ⟨1745998809579017561007467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1163999206386011707338311 1745998809579017561007467)
  ·
    refine ⟨2618998214368526341511201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1745998809579017561007467 2618998214368526341511201)
    ·
      refine ⟨1964248660776394756133401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2618998214368526341511201 1964248660776394756133401)
      ·
        refine ⟨1473186495582296067100051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1964248660776394756133401 1473186495582296067100051)
        ·
          refine ⟨2209779743373444100650077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1473186495582296067100051 2209779743373444100650077)
          ·
            refine ⟨828667403765041537743779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2209779743373444100650077 828667403765041537743779)
            ·
              refine ⟨1243001105647562306615669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 828667403765041537743779 1243001105647562306615669)
              ·
                refine ⟨116531353654458966245219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1243001105647562306615669 116531353654458966245219)
                ·
                  refine ⟨174797030481688449367829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116531353654458966245219 174797030481688449367829)
                  ·
                    refine ⟨8193610803829146064117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 174797030481688449367829 8193610803829146064117)
                    ·
                      rfl

theorem cell23_47871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 5, 1, 6].length) (baseStart_47871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_47871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_47871 prefixEnd_47871 := by exact prefixLift 47871
  have htrace : WordTrace (prefixWord ++ tailWord_47871) baseStart_47871 baseEnd_47871 := by
    simpa [prefixWord, tailWord_47871, baseEnd_47871] using wordTrace_append hprefix tailTrace_47871
  have hstable : (prefixWord ++ tailWord_47871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47871).length < 2 ^ (prefixWord ++ tailWord_47871).sum := by decide
  have hdescent : baseEnd_47871 < baseStart_47871 := by decide
  rcases family_descends (prefixWord ++ tailWord_47871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47881 : List Nat := [1, 2, 1, 1, 3, 2, 2, 2, 3, 1, 5]
def baseStart_47881 : Nat := 118140960795 + 47881 * 2 ^ 59
def prefixEnd_47881 : Nat := 4983230072969 + 3 ^ 40 * 47881 * 2
def baseEnd_47881 : Nat := 24585967218032399067305

theorem tailTrace_47881 : CollatzResearch.WordTrace tailWord_47881 prefixEnd_47881 24585967218032399067305 := by
  unfold tailWord_47881
  simp only [CollatzResearch.WordTrace]
  refine ⟨1746363539542789268871497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1164242359695192845914331 1746363539542789268871497)
  ·
    refine ⟨1309772654657091951653623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1746363539542789268871497 1309772654657091951653623)
    ·
      refine ⟨1964658981985637927480435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1309772654657091951653623 1964658981985637927480435)
      ·
        refine ⟨2946988472978456891220653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1964658981985637927480435 2946988472978456891220653)
        ·
          refine ⟨1105120677366921334207745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2946988472978456891220653 1105120677366921334207745)
          ·
            refine ⟨828840508025191000655809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1105120677366921334207745 828840508025191000655809)
            ·
              refine ⟨621630381018893250491857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 828840508025191000655809 621630381018893250491857)
              ·
                refine ⟨466222785764169937868893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 621630381018893250491857 466222785764169937868893)
                ·
                  refine ⟨174833544661563726700835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 466222785764169937868893 174833544661563726700835)
                  ·
                    refine ⟨262250316992345590051253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 174833544661563726700835 262250316992345590051253)
                    ·
                      refine ⟨24585967218032399067305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 262250316992345590051253 24585967218032399067305)
                      ·
                        rfl

theorem cell23_47881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 3, 1, 5].length) (baseStart_47881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_47881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_47881 prefixEnd_47881 := by exact prefixLift 47881
  have htrace : WordTrace (prefixWord ++ tailWord_47881) baseStart_47881 baseEnd_47881 := by
    simpa [prefixWord, tailWord_47881, baseEnd_47881] using wordTrace_append hprefix tailTrace_47881
  have hstable : (prefixWord ++ tailWord_47881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47881).length < 2 ^ (prefixWord ++ tailWord_47881).sum := by decide
  have hdescent : baseEnd_47881 < baseStart_47881 := by decide
  rcases family_descends (prefixWord ++ tailWord_47881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47905 : List Nat := [1, 2, 3, 2, 1, 2, 4, 2, 2, 4]
def baseStart_47905 : Nat := 118140960795 + 47905 * 2 ^ 59
def prefixEnd_47905 : Nat := 4983230072969 + 3 ^ 40 * 47905 * 2
def baseEnd_47905 : Nat := 8199430251246768389065

theorem tailTrace_47905 : CollatzResearch.WordTrace tailWord_47905 prefixEnd_47905 8199430251246768389065 := by
  unfold tailWord_47905
  simp only [CollatzResearch.WordTrace]
  refine ⟨1747238891455841367745169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1164825927637227578496779 1747238891455841367745169)
  ·
    refine ⟨1310429168591881025808877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1747238891455841367745169 1310429168591881025808877)
    ·
      refine ⟨491410938221955384678329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1310429168591881025808877 491410938221955384678329)
      ·
        refine ⟨368558203666466538508747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 491410938221955384678329 368558203666466538508747)
        ·
          refine ⟨552837305499699807763121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 368558203666466538508747 552837305499699807763121)
          ·
            refine ⟨414627979124774855822341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 552837305499699807763121 414627979124774855822341)
            ·
              refine ⟨77742746085895285466689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 414627979124774855822341 77742746085895285466689)
              ·
                refine ⟨58307059564421464100017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77742746085895285466689 58307059564421464100017)
                ·
                  refine ⟨43730294673316098075013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58307059564421464100017 43730294673316098075013)
                  ·
                    refine ⟨8199430251246768389065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43730294673316098075013 8199430251246768389065)
                    ·
                      rfl

theorem cell23_47905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 2, 2, 4].length) (baseStart_47905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_47905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_47905 prefixEnd_47905 := by exact prefixLift 47905
  have htrace : WordTrace (prefixWord ++ tailWord_47905) baseStart_47905 baseEnd_47905 := by
    simpa [prefixWord, tailWord_47905, baseEnd_47905] using wordTrace_append hprefix tailTrace_47905
  have hstable : (prefixWord ++ tailWord_47905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47905).length < 2 ^ (prefixWord ++ tailWord_47905).sum := by decide
  have hdescent : baseEnd_47905 < baseStart_47905 := by decide
  rcases family_descends (prefixWord ++ tailWord_47905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47906 : List Nat := [3, 3, 1, 1, 2, 4, 2, 2, 1, 1, 3]
def baseStart_47906 : Nat := 118140960795 + 47906 * 2 ^ 59
def prefixEnd_47906 : Nat := 4983230072969 + 3 ^ 40 * 47906 * 2
def baseEnd_47906 : Nat := 24598804234394801254691

theorem tailTrace_47906 : CollatzResearch.WordTrace tailWord_47906 prefixEnd_47906 24598804234394801254691 := by
  unfold tailWord_47906
  simp only [CollatzResearch.WordTrace]
  refine ⟨436818841113054634632893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1164850242968145692354381 436818841113054634632893)
  ·
    refine ⟨163807065417395487987335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 436818841113054634632893 163807065417395487987335)
    ·
      refine ⟨245710598126093231981003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163807065417395487987335 245710598126093231981003)
      ·
        refine ⟨368565897189139847971505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245710598126093231981003 368565897189139847971505)
        ·
          refine ⟨276424422891854885978629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 368565897189139847971505 276424422891854885978629)
          ·
            refine ⟨51829579292222791120993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 276424422891854885978629 51829579292222791120993)
            ·
              refine ⟨38872184469167093340745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51829579292222791120993 38872184469167093340745)
              ·
                refine ⟨29154138351875320005559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38872184469167093340745 29154138351875320005559)
                ·
                  refine ⟨43731207527812980008339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29154138351875320005559 43731207527812980008339)
                  ·
                    refine ⟨65596811291719470012509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43731207527812980008339 65596811291719470012509)
                    ·
                      refine ⟨24598804234394801254691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 65596811291719470012509 24598804234394801254691)
                      ·
                        rfl

theorem cell23_47906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 2, 2, 1, 1, 3].length) (baseStart_47906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_47906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_47906 prefixEnd_47906 := by exact prefixLift 47906
  have htrace : WordTrace (prefixWord ++ tailWord_47906) baseStart_47906 baseEnd_47906 := by
    simpa [prefixWord, tailWord_47906, baseEnd_47906] using wordTrace_append hprefix tailTrace_47906
  have hstable : (prefixWord ++ tailWord_47906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47906).length < 2 ^ (prefixWord ++ tailWord_47906).sum := by decide
  have hdescent : baseEnd_47906 < baseStart_47906 := by decide
  rcases family_descends (prefixWord ++ tailWord_47906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47912 : List Nat := [2, 1, 5, 1, 1, 1, 2, 3, 3, 2, 2]
def baseStart_47912 : Nat := 118140960795 + 47912 * 2 ^ 59
def prefixEnd_47912 : Nat := 4983230072969 + 3 ^ 40 * 47912 * 2
def baseEnd_47912 : Nat := 24601885118321777779663

theorem tailTrace_47912 : CollatzResearch.WordTrace tailWord_47912 prefixEnd_47912 24601885118321777779663 := by
  unfold tailWord_47912
  simp only [CollatzResearch.WordTrace]
  refine ⟨873747101215240781624995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1164996134953654375499993 873747101215240781624995)
  ·
    refine ⟨1310620651822861172437493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 873747101215240781624995 1310620651822861172437493)
    ·
      refine ⟨122870686108393234916015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1310620651822861172437493 122870686108393234916015)
      ·
        refine ⟨184306029162589852374023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122870686108393234916015 184306029162589852374023)
        ·
          refine ⟨276459043743884778561035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184306029162589852374023 276459043743884778561035)
          ·
            refine ⟨414688565615827167841553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276459043743884778561035 414688565615827167841553)
            ·
              refine ⟨311016424211870375881165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 414688565615827167841553 311016424211870375881165)
              ·
                refine ⟨116631159079451390955437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 311016424211870375881165 116631159079451390955437)
                ·
                  refine ⟨43736684654794271608289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 116631159079451390955437 43736684654794271608289)
                  ·
                    refine ⟨32802513491095703706217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43736684654794271608289 32802513491095703706217)
                    ·
                      refine ⟨24601885118321777779663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 32802513491095703706217 24601885118321777779663)
                      ·
                        rfl

theorem cell23_47912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_47912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_47912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_47912 prefixEnd_47912 := by exact prefixLift 47912
  have htrace : WordTrace (prefixWord ++ tailWord_47912) baseStart_47912 baseEnd_47912 := by
    simpa [prefixWord, tailWord_47912, baseEnd_47912] using wordTrace_append hprefix tailTrace_47912
  have hstable : (prefixWord ++ tailWord_47912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47912).length < 2 ^ (prefixWord ++ tailWord_47912).sum := by decide
  have hdescent : baseEnd_47912 < baseStart_47912 := by decide
  rcases family_descends (prefixWord ++ tailWord_47912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47925 : List Nat := [1, 3, 3, 1, 3, 2, 2, 1, 1, 2, 4]
def baseStart_47925 : Nat := 118140960795 + 47925 * 2 ^ 59
def prefixEnd_47925 : Nat := 4983230072969 + 3 ^ 40 * 47925 * 2
def baseEnd_47925 : Nat := 24608560366830226917103

theorem tailTrace_47925 : CollatzResearch.WordTrace tailWord_47925 prefixEnd_47925 24608560366830226917103 := by
  unfold tailWord_47925
  simp only [CollatzResearch.WordTrace]
  refine ⟨1747968351383384783473229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1165312234255589855648819 1747968351383384783473229)
  ·
    refine ⟨655488131768769293802461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1747968351383384783473229 655488131768769293802461)
    ·
      refine ⟨245808049413288485175923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 655488131768769293802461 245808049413288485175923)
      ·
        refine ⟨368712074119932727763885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245808049413288485175923 368712074119932727763885)
        ·
          refine ⟨138267027794974772911457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 368712074119932727763885 138267027794974772911457)
          ·
            refine ⟨103700270846231079683593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138267027794974772911457 103700270846231079683593)
            ·
              refine ⟨77775203134673309762695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103700270846231079683593 77775203134673309762695)
              ·
                refine ⟨116662804702009964644043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77775203134673309762695 116662804702009964644043)
                ·
                  refine ⟨174994207053014946966065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116662804702009964644043 174994207053014946966065)
                  ·
                    refine ⟨131245655289761210224549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 174994207053014946966065 131245655289761210224549)
                    ·
                      refine ⟨24608560366830226917103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 131245655289761210224549 24608560366830226917103)
                      ·
                        rfl

theorem cell23_47925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_47925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_47925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_47925 prefixEnd_47925 := by exact prefixLift 47925
  have htrace : WordTrace (prefixWord ++ tailWord_47925) baseStart_47925 baseEnd_47925 := by
    simpa [prefixWord, tailWord_47925, baseEnd_47925] using wordTrace_append hprefix tailTrace_47925
  have hstable : (prefixWord ++ tailWord_47925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47925).length < 2 ^ (prefixWord ++ tailWord_47925).sum := by decide
  have hdescent : baseEnd_47925 < baseStart_47925 := by decide
  rcases family_descends (prefixWord ++ tailWord_47925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47949 : List Nat := [1, 6, 1, 2, 2, 1, 1, 3, 1, 2, 3]
def baseStart_47949 : Nat := 118140960795 + 47949 * 2 ^ 59
def prefixEnd_47949 : Nat := 4983230072969 + 3 ^ 40 * 47949 * 2
def baseEnd_47949 : Nat := 24620883902538133016993

theorem tailTrace_47949 : CollatzResearch.WordTrace tailWord_47949 prefixEnd_47949 24620883902538133016993 := by
  unfold tailWord_47949
  simp only [CollatzResearch.WordTrace]
  refine ⟨1748843703296436882346901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1165895802197624588231267 1748843703296436882346901)
  ·
    refine ⟨81977048592020478860011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1748843703296436882346901 81977048592020478860011)
    ·
      refine ⟨122965572888030718290017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81977048592020478860011 122965572888030718290017)
      ·
        refine ⟨92224179666023038717513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122965572888030718290017 92224179666023038717513)
        ·
          refine ⟨69168134749517279038135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92224179666023038717513 69168134749517279038135)
          ·
            refine ⟨103752202124275918557203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69168134749517279038135 103752202124275918557203)
            ·
              refine ⟨155628303186413877835805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103752202124275918557203 155628303186413877835805)
              ·
                refine ⟨58360613694905204188427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 155628303186413877835805 58360613694905204188427)
                ·
                  refine ⟨87540920542357806282641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58360613694905204188427 87540920542357806282641)
                  ·
                    refine ⟨65655690406768354711981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 87540920542357806282641 65655690406768354711981)
                    ·
                      refine ⟨24620883902538133016993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 65655690406768354711981 24620883902538133016993)
                      ·
                        rfl

theorem cell23_47949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_47949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_47949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_47949 prefixEnd_47949 := by exact prefixLift 47949
  have htrace : WordTrace (prefixWord ++ tailWord_47949) baseStart_47949 baseEnd_47949 := by
    simpa [prefixWord, tailWord_47949, baseEnd_47949] using wordTrace_append hprefix tailTrace_47949
  have hstable : (prefixWord ++ tailWord_47949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47949).length < 2 ^ (prefixWord ++ tailWord_47949).sum := by decide
  have hdescent : baseEnd_47949 < baseStart_47949 := by decide
  rcases family_descends (prefixWord ++ tailWord_47949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47962 : List Nat := [3, 1, 1, 2, 1, 4, 3, 2, 2, 1, 3]
def baseStart_47962 : Nat := 118140960795 + 47962 * 2 ^ 59
def prefixEnd_47962 : Nat := 4983230072969 + 3 ^ 40 * 47962 * 2
def baseEnd_47962 : Nat := 24627559151046582154433

theorem tailTrace_47962 : CollatzResearch.WordTrace tailWord_47962 prefixEnd_47962 24627559151046582154433 := by
  unfold tailWord_47962
  simp only [CollatzResearch.WordTrace]
  refine ⟨437329463062335025642535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1166211901499560068380093 437329463062335025642535)
  ·
    refine ⟨655994194593502538463803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 437329463062335025642535 655994194593502538463803)
    ·
      refine ⟨983991291890253807695705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 655994194593502538463803 983991291890253807695705)
      ·
        refine ⟨737993468917690355771779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 983991291890253807695705 737993468917690355771779)
        ·
          refine ⟨1106990203376535533657669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 737993468917690355771779 1106990203376535533657669)
          ·
            refine ⟨207560663133100412560813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1106990203376535533657669 207560663133100412560813)
            ·
              refine ⟨77835248674912654710305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 207560663133100412560813 77835248674912654710305)
              ·
                refine ⟨58376436506184491032729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77835248674912654710305 58376436506184491032729)
                ·
                  refine ⟨43782327379638368274547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58376436506184491032729 43782327379638368274547)
                  ·
                    refine ⟨65673491069457552411821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43782327379638368274547 65673491069457552411821)
                    ·
                      refine ⟨24627559151046582154433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 65673491069457552411821 24627559151046582154433)
                      ·
                        rfl

theorem cell23_47962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 2, 2, 1, 3].length) (baseStart_47962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_47962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_47962 prefixEnd_47962 := by exact prefixLift 47962
  have htrace : WordTrace (prefixWord ++ tailWord_47962) baseStart_47962 baseEnd_47962 := by
    simpa [prefixWord, tailWord_47962, baseEnd_47962] using wordTrace_append hprefix tailTrace_47962
  have hstable : (prefixWord ++ tailWord_47962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47962).length < 2 ^ (prefixWord ++ tailWord_47962).sum := by decide
  have hdescent : baseEnd_47962 < baseStart_47962 := by decide
  rcases family_descends (prefixWord ++ tailWord_47962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47989 : List Nat := [1, 3, 4, 1, 1, 3, 2, 2, 1, 3, 2]
def baseStart_47989 : Nat := 118140960795 + 47989 * 2 ^ 59
def prefixEnd_47989 : Nat := 4983230072969 + 3 ^ 40 * 47989 * 2
def baseEnd_47989 : Nat := 24641423128717976516809

theorem tailTrace_47989 : CollatzResearch.WordTrace tailWord_47989 prefixEnd_47989 24641423128717976516809 := by
  unfold tailWord_47989
  simp only [CollatzResearch.WordTrace]
  refine ⟨1750302623151523713803021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1166868415434349142535347 1750302623151523713803021)
  ·
    refine ⟨656363483681821392676133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1750302623151523713803021 656363483681821392676133)
    ·
      refine ⟨123068153190341511126775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 656363483681821392676133 123068153190341511126775)
      ·
        refine ⟨184602229785512266690163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123068153190341511126775 184602229785512266690163)
        ·
          refine ⟨276903344678268400035245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184602229785512266690163 276903344678268400035245)
          ·
            refine ⟨103838754254350650013217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 276903344678268400035245 103838754254350650013217)
            ·
              refine ⟨77879065690762987509913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103838754254350650013217 77879065690762987509913)
              ·
                refine ⟨58409299268072240632435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77879065690762987509913 58409299268072240632435)
                ·
                  refine ⟨87613948902108360948653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58409299268072240632435 87613948902108360948653)
                  ·
                    refine ⟨32855230838290635355745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 87613948902108360948653 32855230838290635355745)
                    ·
                      refine ⟨24641423128717976516809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 32855230838290635355745 24641423128717976516809)
                      ·
                        rfl

theorem cell23_47989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_47989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_47989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_47989 prefixEnd_47989 := by exact prefixLift 47989
  have htrace : WordTrace (prefixWord ++ tailWord_47989) baseStart_47989 baseEnd_47989 := by
    simpa [prefixWord, tailWord_47989, baseEnd_47989] using wordTrace_append hprefix tailTrace_47989
  have hstable : (prefixWord ++ tailWord_47989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47989).length < 2 ^ (prefixWord ++ tailWord_47989).sum := by decide
  have hdescent : baseEnd_47989 < baseStart_47989 := by decide
  rcases family_descends (prefixWord ++ tailWord_47989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48075 : List Nat := [1, 1, 1, 1, 3, 5, 2, 2, 2, 1, 4]
def baseStart_48075 : Nat := 118140960795 + 48075 * 2 ^ 59
def prefixEnd_48075 : Nat := 4983230072969 + 3 ^ 40 * 48075 * 2
def baseEnd_48075 : Nat := 24685582465004640041413

theorem tailTrace_48075 : CollatzResearch.WordTrace tailWord_48075 prefixEnd_48075 24685582465004640041413 := by
  unfold tailWord_48075
  simp only [CollatzResearch.WordTrace]
  refine ⟨1753439300839960401433679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1168959533893306934289119 1753439300839960401433679)
  ·
    refine ⟨2630158951259940602150519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1753439300839960401433679 2630158951259940602150519)
    ·
      refine ⟨3945238426889910903225779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2630158951259940602150519 3945238426889910903225779)
      ·
        refine ⟨5917857640334866354838669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3945238426889910903225779 5917857640334866354838669)
        ·
          refine ⟨2219196615125574883064501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5917857640334866354838669 2219196615125574883064501)
          ·
            refine ⟨208049682668022645287297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2219196615125574883064501 208049682668022645287297)
            ·
              refine ⟨156037262001016983965473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208049682668022645287297 156037262001016983965473)
              ·
                refine ⟨117027946500762737974105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156037262001016983965473 117027946500762737974105)
                ·
                  refine ⟨87770959875572053480579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117027946500762737974105 87770959875572053480579)
                  ·
                    refine ⟨131656439813358080220869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 87770959875572053480579 131656439813358080220869)
                    ·
                      refine ⟨24685582465004640041413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 131656439813358080220869 24685582465004640041413)
                      ·
                        rfl

theorem cell23_48075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 2, 2, 1, 4].length) (baseStart_48075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_48075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_48075 prefixEnd_48075 := by exact prefixLift 48075
  have htrace : WordTrace (prefixWord ++ tailWord_48075) baseStart_48075 baseEnd_48075 := by
    simpa [prefixWord, tailWord_48075, baseEnd_48075] using wordTrace_append hprefix tailTrace_48075
  have hstable : (prefixWord ++ tailWord_48075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48075).length < 2 ^ (prefixWord ++ tailWord_48075).sum := by decide
  have hdescent : baseEnd_48075 < baseStart_48075 := by decide
  rcases family_descends (prefixWord ++ tailWord_48075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48152 : List Nat := [2, 1, 2, 3, 2, 2, 1, 2, 1, 5, 2]
def baseStart_48152 : Nat := 118140960795 + 48152 * 2 ^ 59
def prefixEnd_48152 : Nat := 4983230072969 + 3 ^ 40 * 48152 * 2
def baseEnd_48152 : Nat := 24725120475400838778559

theorem tailTrace_48152 : CollatzResearch.WordTrace tailWord_48152 prefixEnd_48152 24725120475400838778559 := by
  unfold tailWord_48152
  simp only [CollatzResearch.WordTrace]
  refine ⟨878123860780501275993355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1170831814374001701324473 878123860780501275993355)
  ·
    refine ⟨1317185791170751913990033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 878123860780501275993355 1317185791170751913990033)
    ·
      refine ⟨987889343378063935492525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1317185791170751913990033 987889343378063935492525)
      ·
        refine ⟨370458503766773975809697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 987889343378063935492525 370458503766773975809697)
        ·
          refine ⟨277843877825080481857273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 370458503766773975809697 277843877825080481857273)
          ·
            refine ⟨208382908368810361392955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 277843877825080481857273 208382908368810361392955)
            ·
              refine ⟨312574362553215542089433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208382908368810361392955 312574362553215542089433)
              ·
                refine ⟨234430771914911656567075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 312574362553215542089433 234430771914911656567075)
                ·
                  refine ⟨351646157872367484850613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 234430771914911656567075 351646157872367484850613)
                  ·
                    refine ⟨32966827300534451704745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 351646157872367484850613 32966827300534451704745)
                    ·
                      refine ⟨24725120475400838778559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 32966827300534451704745 24725120475400838778559)
                      ·
                        rfl

theorem cell23_48152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 1, 5, 2].length) (baseStart_48152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_48152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_48152 prefixEnd_48152 := by exact prefixLift 48152
  have htrace : WordTrace (prefixWord ++ tailWord_48152) baseStart_48152 baseEnd_48152 := by
    simpa [prefixWord, tailWord_48152, baseEnd_48152] using wordTrace_append hprefix tailTrace_48152
  have hstable : (prefixWord ++ tailWord_48152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48152).length < 2 ^ (prefixWord ++ tailWord_48152).sum := by decide
  have hdescent : baseEnd_48152 < baseStart_48152 := by decide
  rcases family_descends (prefixWord ++ tailWord_48152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48162 : List Nat := [3, 3, 1, 1, 1, 3, 1, 4, 1, 5]
def baseStart_48162 : Nat := 118140960795 + 48162 * 2 ^ 59
def prefixEnd_48162 : Nat := 4983230072969 + 3 ^ 40 * 48162 * 2
def baseEnd_48162 : Nat := 8243418427315266551171

theorem tailTrace_48162 : CollatzResearch.WordTrace tailWord_48162 prefixEnd_48162 8243418427315266551171 := by
  unfold tailWord_48162
  simp only [CollatzResearch.WordTrace]
  refine ⟨439153112881193564962685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1171074967683182839900493 439153112881193564962685)
  ·
    refine ⟨164682417330447586861007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 439153112881193564962685 164682417330447586861007)
    ·
      refine ⟨247023625995671380291511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164682417330447586861007 247023625995671380291511)
      ·
        refine ⟨370535438993507070437267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247023625995671380291511 370535438993507070437267)
        ·
          refine ⟨555803158490260605655901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 370535438993507070437267 555803158490260605655901)
          ·
            refine ⟨208426184433847727120963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 555803158490260605655901 208426184433847727120963)
            ·
              refine ⟨312639276650771590681445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208426184433847727120963 312639276650771590681445)
              ·
                refine ⟨58619864372019673252771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 312639276650771590681445 58619864372019673252771)
                ·
                  refine ⟨87929796558029509879157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58619864372019673252771 87929796558029509879157)
                  ·
                    refine ⟨8243418427315266551171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 87929796558029509879157 8243418427315266551171)
                    ·
                      rfl

theorem cell23_48162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_48162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_48162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_48162 prefixEnd_48162 := by exact prefixLift 48162
  have htrace : WordTrace (prefixWord ++ tailWord_48162) baseStart_48162 baseEnd_48162 := by
    simpa [prefixWord, tailWord_48162, baseEnd_48162] using wordTrace_append hprefix tailTrace_48162
  have hstable : (prefixWord ++ tailWord_48162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48162).length < 2 ^ (prefixWord ++ tailWord_48162).sum := by decide
  have hdescent : baseEnd_48162 < baseStart_48162 := by decide
  rcases family_descends (prefixWord ++ tailWord_48162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48192 : List Nat := [2, 1, 1, 2, 2, 3, 2, 4, 2, 4]
def baseStart_48192 : Nat := 118140960795 + 48192 * 2 ^ 59
def prefixEnd_48192 : Nat := 4983230072969 + 3 ^ 40 * 48192 * 2
def baseEnd_48192 : Nat := 8248553233860227426125

theorem tailTrace_48192 : CollatzResearch.WordTrace tailWord_48192 prefixEnd_48192 8248553233860227426125 := by
  unfold tailWord_48192
  simp only [CollatzResearch.WordTrace]
  refine ⟨878853320708044691721415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1171804427610726255628553 878853320708044691721415)
  ·
    refine ⟨1318279981062067037582123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 878853320708044691721415 1318279981062067037582123)
    ·
      refine ⟨1977419971593100556373185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1318279981062067037582123 1977419971593100556373185)
      ·
        refine ⟨1483064978694825417279889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1977419971593100556373185 1483064978694825417279889)
        ·
          refine ⟨1112298734021119062959917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1483064978694825417279889 1112298734021119062959917)
          ·
            refine ⟨417112025257919648609969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1112298734021119062959917 417112025257919648609969)
            ·
              refine ⟨312834018943439736457477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 417112025257919648609969 312834018943439736457477)
              ·
                refine ⟨58656378551894950585777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 312834018943439736457477 58656378551894950585777)
                ·
                  refine ⟨43992283913921212939333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58656378551894950585777 43992283913921212939333)
                  ·
                    refine ⟨8248553233860227426125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43992283913921212939333 8248553233860227426125)
                    ·
                      rfl

theorem cell23_48192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 4, 2, 4].length) (baseStart_48192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_48192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_48192 prefixEnd_48192 := by exact prefixLift 48192
  have htrace : WordTrace (prefixWord ++ tailWord_48192) baseStart_48192 baseEnd_48192 := by
    simpa [prefixWord, tailWord_48192, baseEnd_48192] using wordTrace_append hprefix tailTrace_48192
  have hstable : (prefixWord ++ tailWord_48192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48192).length < 2 ^ (prefixWord ++ tailWord_48192).sum := by decide
  have hdescent : baseEnd_48192 < baseStart_48192 := by decide
  rcases family_descends (prefixWord ++ tailWord_48192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48193 : List Nat := [1, 2, 5, 1, 4, 1, 1, 1, 3, 1, 3]
def baseStart_48193 : Nat := 118140960795 + 48193 * 2 ^ 59
def prefixEnd_48193 : Nat := 4983230072969 + 3 ^ 40 * 48193 * 2
def baseEnd_48193 : Nat := 24746173182235178365871

theorem tailTrace_48193 : CollatzResearch.WordTrace tailWord_48193 prefixEnd_48193 24746173182235178365871 := by
  unfold tailWord_48193
  simp only [CollatzResearch.WordTrace]
  refine ⟨1757743114412466554229233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1171828742941644369486155 1757743114412466554229233)
  ·
    refine ⟨1318307335809349915671925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1757743114412466554229233 1318307335809349915671925)
    ·
      refine ⟨123591312732126554594243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1318307335809349915671925 123591312732126554594243)
      ·
        refine ⟨185386969098189831891365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123591312732126554594243 185386969098189831891365)
        ·
          refine ⟨34760056705910593479631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 185386969098189831891365 34760056705910593479631)
          ·
            refine ⟨52140085058865890219447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34760056705910593479631 52140085058865890219447)
            ·
              refine ⟨78210127588298835329171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52140085058865890219447 78210127588298835329171)
              ·
                refine ⟨117315191382448252993757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78210127588298835329171 117315191382448252993757)
                ·
                  refine ⟨43993196768418094872659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 117315191382448252993757 43993196768418094872659)
                  ·
                    refine ⟨65989795152627142308989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43993196768418094872659 65989795152627142308989)
                    ·
                      refine ⟨24746173182235178365871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 65989795152627142308989 24746173182235178365871)
                      ·
                        rfl

theorem cell23_48193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_48193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_48193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_48193 prefixEnd_48193 := by exact prefixLift 48193
  have htrace : WordTrace (prefixWord ++ tailWord_48193) baseStart_48193 baseEnd_48193 := by
    simpa [prefixWord, tailWord_48193, baseEnd_48193] using wordTrace_append hprefix tailTrace_48193
  have hstable : (prefixWord ++ tailWord_48193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48193).length < 2 ^ (prefixWord ++ tailWord_48193).sum := by decide
  have hdescent : baseEnd_48193 < baseStart_48193 := by decide
  rcases family_descends (prefixWord ++ tailWord_48193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48209 : List Nat := [1, 2, 2, 1, 3, 1, 6, 1, 2, 4]
def baseStart_48209 : Nat := 118140960795 + 48209 * 2 ^ 59
def prefixEnd_48209 : Nat := 4983230072969 + 3 ^ 40 * 48209 * 2
def baseEnd_48209 : Nat := 8251462957569038588599

theorem tailTrace_48209 : CollatzResearch.WordTrace tailWord_48209 prefixEnd_48209 8251462957569038588599 := by
  unfold tailWord_48209
  simp only [CollatzResearch.WordTrace]
  refine ⟨1758326682354501286811681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1172217788236334191207787 1758326682354501286811681)
  ·
    refine ⟨1318745011765875965108761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1758326682354501286811681 1318745011765875965108761)
    ·
      refine ⟨989058758824406973831571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1318745011765875965108761 989058758824406973831571)
      ·
        refine ⟨1483588138236610460747357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 989058758824406973831571 1483588138236610460747357)
        ·
          refine ⟨556345551838728922780259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1483588138236610460747357 556345551838728922780259)
          ·
            refine ⟨834518327758093384170389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 556345551838728922780259 834518327758093384170389)
            ·
              refine ⟨39118046613660627382987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 834518327758093384170389 39118046613660627382987)
              ·
                refine ⟨58677069920490941074481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39118046613660627382987 58677069920490941074481)
                ·
                  refine ⟨44007802440368205805861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58677069920490941074481 44007802440368205805861)
                  ·
                    refine ⟨8251462957569038588599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44007802440368205805861 8251462957569038588599)
                    ·
                      rfl

theorem cell23_48209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6, 1, 2, 4].length) (baseStart_48209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_48209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_48209 prefixEnd_48209 := by exact prefixLift 48209
  have htrace : WordTrace (prefixWord ++ tailWord_48209) baseStart_48209 baseEnd_48209 := by
    simpa [prefixWord, tailWord_48209, baseEnd_48209] using wordTrace_append hprefix tailTrace_48209
  have hstable : (prefixWord ++ tailWord_48209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48209).length < 2 ^ (prefixWord ++ tailWord_48209).sum := by decide
  have hdescent : baseEnd_48209 < baseStart_48209 := by decide
  rcases family_descends (prefixWord ++ tailWord_48209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48265 : List Nat := [1, 2, 1, 1, 4, 3, 1, 1, 1, 8]
def baseStart_48265 : Nat := 118140960795 + 48265 * 2 ^ 59
def prefixEnd_48265 : Nat := 4983230072969 + 3 ^ 40 * 48265 * 2
def baseEnd_48265 : Nat := 8261047929786298888513

theorem tailTrace_48265 : CollatzResearch.WordTrace tailWord_48265 prefixEnd_48265 8261047929786298888513 := by
  unfold tailWord_48265
  simp only [CollatzResearch.WordTrace]
  refine ⟨1760369170151622850850249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1173579446767748567233499 1760369170151622850850249)
  ·
    refine ⟨1320276877613717138137687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1760369170151622850850249 1320276877613717138137687)
    ·
      refine ⟨1980415316420575707206531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1320276877613717138137687 1980415316420575707206531)
      ·
        refine ⟨2970622974630863560809797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1980415316420575707206531 2970622974630863560809797)
        ·
          refine ⟨556991807743286917651837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2970622974630863560809797 556991807743286917651837)
          ·
            refine ⟨208871927903732594119439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 556991807743286917651837 208871927903732594119439)
            ·
              refine ⟨313307891855598891179159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208871927903732594119439 313307891855598891179159)
              ·
                refine ⟨469961837783398336768739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 313307891855598891179159 469961837783398336768739)
                ·
                  refine ⟨704942756675097505153109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 469961837783398336768739 704942756675097505153109)
                  ·
                    refine ⟨8261047929786298888513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 704942756675097505153109 8261047929786298888513)
                    ·
                      rfl

theorem cell23_48265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 8].length) (baseStart_48265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_48265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_48265 prefixEnd_48265 := by exact prefixLift 48265
  have htrace : WordTrace (prefixWord ++ tailWord_48265) baseStart_48265 baseEnd_48265 := by
    simpa [prefixWord, tailWord_48265, baseEnd_48265] using wordTrace_append hprefix tailTrace_48265
  have hstable : (prefixWord ++ tailWord_48265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48265).length < 2 ^ (prefixWord ++ tailWord_48265).sum := by decide
  have hdescent : baseEnd_48265 < baseStart_48265 := by decide
  rcases family_descends (prefixWord ++ tailWord_48265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48275 : List Nat := [1, 1, 1, 2, 1, 2, 4, 1, 4, 1, 5]
def baseStart_48275 : Nat := 118140960795 + 48275 * 2 ^ 59
def prefixEnd_48275 : Nat := 4983230072969 + 3 ^ 40 * 48275 * 2
def baseEnd_48275 : Nat := 24788278595903857540493

theorem tailTrace_48275 : CollatzResearch.WordTrace tailWord_48275 prefixEnd_48275 24788278595903857540493 := by
  unfold tailWord_48275
  simp only [CollatzResearch.WordTrace]
  refine ⟨1760733900115394558714279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1173822600076929705809519 1760733900115394558714279)
  ·
    refine ⟨2641100850173091838071419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1760733900115394558714279 2641100850173091838071419)
    ·
      refine ⟨3961651275259637757107129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2641100850173091838071419 3961651275259637757107129)
      ·
        refine ⟨2971238456444728317830347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3961651275259637757107129 2971238456444728317830347)
        ·
          refine ⟨4456857684667092476745521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2971238456444728317830347 4456857684667092476745521)
          ·
            refine ⟨3342643263500319357559141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4456857684667092476745521 3342643263500319357559141)
            ·
              refine ⟨626745611906309879542339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3342643263500319357559141 626745611906309879542339)
              ·
                refine ⟨940118417859464819313509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 626745611906309879542339 940118417859464819313509)
                ·
                  refine ⟨176272203348649653621283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 940118417859464819313509 176272203348649653621283)
                  ·
                    refine ⟨264408305022974480431925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 176272203348649653621283 264408305022974480431925)
                    ·
                      refine ⟨24788278595903857540493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 264408305022974480431925 24788278595903857540493)
                      ·
                        rfl

theorem cell23_48275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 4, 1, 5].length) (baseStart_48275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_48275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_48275 prefixEnd_48275 := by exact prefixLift 48275
  have htrace : WordTrace (prefixWord ++ tailWord_48275) baseStart_48275 baseEnd_48275 := by
    simpa [prefixWord, tailWord_48275, baseEnd_48275] using wordTrace_append hprefix tailTrace_48275
  have hstable : (prefixWord ++ tailWord_48275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48275).length < 2 ^ (prefixWord ++ tailWord_48275).sum := by decide
  have hdescent : baseEnd_48275 < baseStart_48275 := by decide
  rcases family_descends (prefixWord ++ tailWord_48275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48289 : List Nat := [1, 2, 3, 3, 1, 1, 1, 4, 1, 4, 2]
def baseStart_48289 : Nat := 118140960795 + 48289 * 2 ^ 59
def prefixEnd_48289 : Nat := 4983230072969 + 3 ^ 40 * 48289 * 2
def baseEnd_48289 : Nat := 24795467325066802765429

theorem tailTrace_48289 : CollatzResearch.WordTrace tailWord_48289 prefixEnd_48289 24795467325066802765429 := by
  unfold tailWord_48289
  simp only [CollatzResearch.WordTrace]
  refine ⟨1761244522064674949723921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1174163014709783299815947 1761244522064674949723921)
  ·
    refine ⟨1320933391548506212292941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1761244522064674949723921 1320933391548506212292941)
    ·
      refine ⟨495350021830689829609853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1320933391548506212292941 495350021830689829609853)
      ·
        refine ⟨185756258186508686103695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 495350021830689829609853 185756258186508686103695)
        ·
          refine ⟨278634387279763029155543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185756258186508686103695 278634387279763029155543)
          ·
            refine ⟨417951580919644543733315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278634387279763029155543 417951580919644543733315)
            ·
              refine ⟨626927371379466815599973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 417951580919644543733315 626927371379466815599973)
              ·
                refine ⟨117548882133650027924995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 626927371379466815599973 117548882133650027924995)
                ·
                  refine ⟨176323323200475041887493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117548882133650027924995 176323323200475041887493)
                  ·
                    refine ⟨33060623100089070353905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 176323323200475041887493 33060623100089070353905)
                    ·
                      refine ⟨24795467325066802765429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 33060623100089070353905 24795467325066802765429)
                      ·
                        rfl

theorem cell23_48289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_48289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_48289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_48289 prefixEnd_48289 := by exact prefixLift 48289
  have htrace : WordTrace (prefixWord ++ tailWord_48289) baseStart_48289 baseEnd_48289 := by
    simpa [prefixWord, tailWord_48289, baseEnd_48289] using wordTrace_append hprefix tailTrace_48289
  have hstable : (prefixWord ++ tailWord_48289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48289).length < 2 ^ (prefixWord ++ tailWord_48289).sum := by decide
  have hdescent : baseEnd_48289 < baseStart_48289 := by decide
  rcases family_descends (prefixWord ++ tailWord_48289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48293 : List Nat := [1, 3, 1, 2, 1, 6, 2, 1, 1, 3, 2]
def baseStart_48293 : Nat := 118140960795 + 48293 * 2 ^ 59
def prefixEnd_48293 : Nat := 4983230072969 + 3 ^ 40 * 48293 * 2
def baseEnd_48293 : Nat := 24797521247684787115411

theorem tailTrace_48293 : CollatzResearch.WordTrace tailWord_48293 prefixEnd_48293 24797521247684787115411 := by
  unfold tailWord_48293
  simp only [CollatzResearch.WordTrace]
  refine ⟨1761390414050183632869533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1174260276033455755246355 1761390414050183632869533)
  ·
    refine ⟨660521405268818862326075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1761390414050183632869533 660521405268818862326075)
    ·
      refine ⟨990782107903228293489113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 660521405268818862326075 990782107903228293489113)
      ·
        refine ⟨743086580927421220116835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 990782107903228293489113 743086580927421220116835)
        ·
          refine ⟨1114629871391131830175253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 743086580927421220116835 1114629871391131830175253)
          ·
            refine ⟨52248275221459304539465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1114629871391131830175253 52248275221459304539465)
            ·
              refine ⟨39186206416094478404599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52248275221459304539465 39186206416094478404599)
              ·
                refine ⟨58779309624141717606899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39186206416094478404599 58779309624141717606899)
                ·
                  refine ⟨88168964436212576410349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58779309624141717606899 88168964436212576410349)
                  ·
                    refine ⟨33063361663579716153881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 88168964436212576410349 33063361663579716153881)
                    ·
                      refine ⟨24797521247684787115411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 33063361663579716153881 24797521247684787115411)
                      ·
                        rfl

theorem cell23_48293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 2, 1, 1, 3, 2].length) (baseStart_48293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_48293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_48293 prefixEnd_48293 := by exact prefixLift 48293
  have htrace : WordTrace (prefixWord ++ tailWord_48293) baseStart_48293 baseEnd_48293 := by
    simpa [prefixWord, tailWord_48293, baseEnd_48293] using wordTrace_append hprefix tailTrace_48293
  have hstable : (prefixWord ++ tailWord_48293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48293).length < 2 ^ (prefixWord ++ tailWord_48293).sum := by decide
  have hdescent : baseEnd_48293 < baseStart_48293 := by decide
  rcases family_descends (prefixWord ++ tailWord_48293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48306 : List Nat := [3, 2, 1, 1, 1, 5, 1, 1, 4, 2, 2]
def baseStart_48306 : Nat := 118140960795 + 48306 * 2 ^ 59
def prefixEnd_48306 : Nat := 4983230072969 + 3 ^ 40 * 48306 * 2
def baseEnd_48306 : Nat := 24804196496193236252851

theorem tailTrace_48306 : CollatzResearch.WordTrace tailWord_48306 prefixEnd_48306 24804196496193236252851 := by
  unfold tailWord_48306
  simp only [CollatzResearch.WordTrace]
  refine ⟨440466140750771713273193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1174576375335391235395181 440466140750771713273193)
  ·
    refine ⟨330349605563078784954895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 440466140750771713273193 330349605563078784954895)
    ·
      refine ⟨495524408344618177432343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330349605563078784954895 495524408344618177432343)
      ·
        refine ⟨743286612516927266148515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 495524408344618177432343 743286612516927266148515)
        ·
          refine ⟨1114929918775390899222773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 743286612516927266148515 1114929918775390899222773)
          ·
            refine ⟨104524679885192896802135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1114929918775390899222773 104524679885192896802135)
            ·
              refine ⟨156787019827789345203203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104524679885192896802135 156787019827789345203203)
              ·
                refine ⟨235180529741684017804805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156787019827789345203203 235180529741684017804805)
                ·
                  refine ⟨44096349326565753338401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 235180529741684017804805 44096349326565753338401)
                  ·
                    refine ⟨33072261994924315003801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44096349326565753338401 33072261994924315003801)
                    ·
                      refine ⟨24804196496193236252851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 33072261994924315003801 24804196496193236252851)
                      ·
                        rfl

theorem cell23_48306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 4, 2, 2].length) (baseStart_48306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_48306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_48306 prefixEnd_48306 := by exact prefixLift 48306
  have htrace : WordTrace (prefixWord ++ tailWord_48306) baseStart_48306 baseEnd_48306 := by
    simpa [prefixWord, tailWord_48306, baseEnd_48306] using wordTrace_append hprefix tailTrace_48306
  have hstable : (prefixWord ++ tailWord_48306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48306).length < 2 ^ (prefixWord ++ tailWord_48306).sum := by decide
  have hdescent : baseEnd_48306 < baseStart_48306 := by decide
  rcases family_descends (prefixWord ++ tailWord_48306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48335 : List Nat := [1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 7]
def baseStart_48335 : Nat := 118140960795 + 48335 * 2 ^ 59
def prefixEnd_48335 : Nat := 4983230072969 + 3 ^ 40 * 48335 * 2
def baseEnd_48335 : Nat := 24819087435173622790217

theorem tailTrace_48335 : CollatzResearch.WordTrace tailWord_48335 prefixEnd_48335 24819087435173622790217 := by
  unfold tailWord_48335
  simp only [CollatzResearch.WordTrace]
  refine ⟨1762922279898024805898459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1175281519932016537265639 1762922279898024805898459)
  ·
    refine ⟨2644383419847037208847689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1762922279898024805898459 2644383419847037208847689)
    ·
      refine ⟨1983287564885277906635767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2644383419847037208847689 1983287564885277906635767)
      ·
        refine ⟨2974931347327916859953651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1983287564885277906635767 2974931347327916859953651)
        ·
          refine ⟨4462397020991875289930477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2974931347327916859953651 4462397020991875289930477)
          ·
            refine ⟨1673398882871953233723929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4462397020991875289930477 1673398882871953233723929)
            ·
              refine ⟨1255049162153964925292947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1673398882871953233723929 1255049162153964925292947)
              ·
                refine ⟨1882573743230947387939421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1255049162153964925292947 1882573743230947387939421)
                ·
                  refine ⟨705965153711605270477283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1882573743230947387939421 705965153711605270477283)
                  ·
                    refine ⟨1058947730567407905715925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 705965153711605270477283 1058947730567407905715925)
                    ·
                      refine ⟨24819087435173622790217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 1058947730567407905715925 24819087435173622790217)
                      ·
                        rfl

theorem cell23_48335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 7].length) (baseStart_48335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_48335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_48335 prefixEnd_48335 := by exact prefixLift 48335
  have htrace : WordTrace (prefixWord ++ tailWord_48335) baseStart_48335 baseEnd_48335 := by
    simpa [prefixWord, tailWord_48335, baseEnd_48335] using wordTrace_append hprefix tailTrace_48335
  have hstable : (prefixWord ++ tailWord_48335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48335).length < 2 ^ (prefixWord ++ tailWord_48335).sum := by decide
  have hdescent : baseEnd_48335 < baseStart_48335 := by decide
  rcases family_descends (prefixWord ++ tailWord_48335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48419 : List Nat := [1, 1, 1, 4, 2, 4, 2, 2, 6]
def baseStart_48419 : Nat := 118140960795 + 48419 * 2 ^ 59
def prefixEnd_48419 : Nat := 4983230072969 + 3 ^ 40 * 48419 * 2
def baseEnd_48419 : Nat := 2762468867794588237759

theorem tailTrace_48419 : CollatzResearch.WordTrace tailWord_48419 prefixEnd_48419 2762468867794588237759 := by
  unfold tailWord_48419
  simp only [CollatzResearch.WordTrace]
  refine ⟨1765986011593707151956311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1177324007729138101304207 1765986011593707151956311)
  ·
    refine ⟨2648979017390560727934467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1765986011593707151956311 2648979017390560727934467)
    ·
      refine ⟨3973468526085841091901701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2648979017390560727934467 3973468526085841091901701)
      ·
        refine ⟨745025348641095204731569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3973468526085841091901701 745025348641095204731569)
        ·
          refine ⟨558769011480821403548677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 745025348641095204731569 558769011480821403548677)
          ·
            refine ⟨104769189652654013165377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 558769011480821403548677 104769189652654013165377)
            ·
              refine ⟨78576892239490509874033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104769189652654013165377 78576892239490509874033)
              ·
                refine ⟨58932669179617882405525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78576892239490509874033 58932669179617882405525)
                ·
                  refine ⟨2762468867794588237759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 58932669179617882405525 2762468867794588237759)
                  ·
                    rfl

theorem cell23_48419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 2, 6].length) (baseStart_48419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_48419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_48419 prefixEnd_48419 := by exact prefixLift 48419
  have htrace : WordTrace (prefixWord ++ tailWord_48419) baseStart_48419 baseEnd_48419 := by
    simpa [prefixWord, tailWord_48419, baseEnd_48419] using wordTrace_append hprefix tailTrace_48419
  have hstable : (prefixWord ++ tailWord_48419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48419).length < 2 ^ (prefixWord ++ tailWord_48419).sum := by decide
  have hdescent : baseEnd_48419 < baseStart_48419 := by decide
  rcases family_descends (prefixWord ++ tailWord_48419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48432 : List Nat := [2, 1, 1, 1, 2, 2, 3, 1, 5, 5]
def baseStart_48432 : Nat := 118140960795 + 48432 * 2 ^ 59
def prefixEnd_48432 : Nat := 4983230072969 + 3 ^ 40 * 48432 * 2
def baseEnd_48432 : Nat := 8289631686219914425757

theorem tailTrace_48432 : CollatzResearch.WordTrace tailWord_48432 prefixEnd_48432 8289631686219914425757 := by
  unfold tailWord_48432
  simp only [CollatzResearch.WordTrace]
  refine ⟨883230080273305186089775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1177640107031073581453033 883230080273305186089775)
  ·
    refine ⟨1324845120409957779134663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 883230080273305186089775 1324845120409957779134663)
    ·
      refine ⟨1987267680614936668701995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1324845120409957779134663 1987267680614936668701995)
      ·
        refine ⟨2980901520922405003052993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1987267680614936668701995 2980901520922405003052993)
        ·
          refine ⟨2235676140691803752289745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2980901520922405003052993 2235676140691803752289745)
          ·
            refine ⟨1676757105518852814217309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2235676140691803752289745 1676757105518852814217309)
            ·
              refine ⟨628783914569569805331491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1676757105518852814217309 628783914569569805331491)
              ·
                refine ⟨943175871854354707997237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 628783914569569805331491 943175871854354707997237)
                ·
                  refine ⟨88422737986345753874741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 943175871854354707997237 88422737986345753874741)
                  ·
                    refine ⟨8289631686219914425757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 88422737986345753874741 8289631686219914425757)
                    ·
                      rfl

theorem cell23_48432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 5, 5].length) (baseStart_48432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_48432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_48432 prefixEnd_48432 := by exact prefixLift 48432
  have htrace : WordTrace (prefixWord ++ tailWord_48432) baseStart_48432 baseEnd_48432 := by
    simpa [prefixWord, tailWord_48432, baseEnd_48432] using wordTrace_append hprefix tailTrace_48432
  have hstable : (prefixWord ++ tailWord_48432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48432).length < 2 ^ (prefixWord ++ tailWord_48432).sum := by decide
  have hdescent : baseEnd_48432 < baseStart_48432 := by decide
  rcases family_descends (prefixWord ++ tailWord_48432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48442 : List Nat := [3, 1, 1, 1, 4, 1, 1, 1, 2, 1, 7]
def baseStart_48442 : Nat := 118140960795 + 48442 * 2 ^ 59
def prefixEnd_48442 : Nat := 4983230072969 + 3 ^ 40 * 48442 * 2
def baseEnd_48442 : Nat := 24874029865204704152225

theorem tailTrace_48442 : CollatzResearch.WordTrace tailWord_48442 prefixEnd_48442 24874029865204704152225 := by
  unfold tailWord_48442
  simp only [CollatzResearch.WordTrace]
  refine ⟨441706222627595520010895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1177883260340254720029053 441706222627595520010895)
  ·
    refine ⟨662559333941393280016343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 441706222627595520010895 662559333941393280016343)
    ·
      refine ⟨993839000912089920024515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 662559333941393280016343 993839000912089920024515)
      ·
        refine ⟨1490758501368134880036773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 993839000912089920024515 1490758501368134880036773)
        ·
          refine ⟨279517219006525290006895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1490758501368134880036773 279517219006525290006895)
          ·
            refine ⟨419275828509787935010343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279517219006525290006895 419275828509787935010343)
            ·
              refine ⟨628913742764681902515515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 419275828509787935010343 628913742764681902515515)
              ·
                refine ⟨943370614147022853773273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 628913742764681902515515 943370614147022853773273)
                ·
                  refine ⟨707527960610267140329955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 943370614147022853773273 707527960610267140329955)
                  ·
                    refine ⟨1061291940915400710494933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 707527960610267140329955 1061291940915400710494933)
                    ·
                      refine ⟨24874029865204704152225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 1061291940915400710494933 24874029865204704152225)
                      ·
                        rfl

theorem cell23_48442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 2, 1, 7].length) (baseStart_48442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_48442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_48442 prefixEnd_48442 := by exact prefixLift 48442
  have htrace : WordTrace (prefixWord ++ tailWord_48442) baseStart_48442 baseEnd_48442 := by
    simpa [prefixWord, tailWord_48442, baseEnd_48442] using wordTrace_append hprefix tailTrace_48442
  have hstable : (prefixWord ++ tailWord_48442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48442).length < 2 ^ (prefixWord ++ tailWord_48442).sum := by decide
  have hdescent : baseEnd_48442 < baseStart_48442 := by decide
  rcases family_descends (prefixWord ++ tailWord_48442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48470 : List Nat := [5, 2, 3, 1, 1, 1, 1, 1, 8]
def baseStart_48470 : Nat := 118140960795 + 48470 * 2 ^ 59
def prefixEnd_48470 : Nat := 4983230072969 + 3 ^ 40 * 48470 * 2
def baseEnd_48470 : Nat := 2765378591503399400233

theorem tailTrace_48470 : CollatzResearch.WordTrace tailWord_48470 prefixEnd_48470 2765378591503399400233 := by
  unfold tailWord_48470
  simp only [CollatzResearch.WordTrace]
  refine ⟨110490383400558928878929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1178564089605961908041909 110490383400558928878929)
  ·
    refine ⟨82867787550419196659197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110490383400558928878929 82867787550419196659197)
    ·
      refine ⟨31075420331407198747199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82867787550419196659197 31075420331407198747199)
      ·
        refine ⟨46613130497110798120799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31075420331407198747199 46613130497110798120799)
        ·
          refine ⟨69919695745666197181199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46613130497110798120799 69919695745666197181199)
          ·
            refine ⟨104879543618499295771799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69919695745666197181199 104879543618499295771799)
            ·
              refine ⟨157319315427748943657699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104879543618499295771799 157319315427748943657699)
              ·
                refine ⟨235978973141623415486549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157319315427748943657699 235978973141623415486549)
                ·
                  refine ⟨2765378591503399400233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 235978973141623415486549 2765378591503399400233)
                  ·
                    rfl

theorem cell23_48470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_48470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_48470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_48470 prefixEnd_48470 := by exact prefixLift 48470
  have htrace : WordTrace (prefixWord ++ tailWord_48470) baseStart_48470 baseEnd_48470 := by
    simpa [prefixWord, tailWord_48470, baseEnd_48470] using wordTrace_append hprefix tailTrace_48470
  have hstable : (prefixWord ++ tailWord_48470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48470).length < 2 ^ (prefixWord ++ tailWord_48470).sum := by decide
  have hdescent : baseEnd_48470 < baseStart_48470 := by decide
  rcases family_descends (prefixWord ++ tailWord_48470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48489 : List Nat := [1, 2, 1, 1, 1, 3, 2, 4, 3, 2, 3]
def baseStart_48489 : Nat := 118140960795 + 48489 * 2 ^ 59
def prefixEnd_48489 : Nat := 4983230072969 + 3 ^ 40 * 48489 * 2
def baseEnd_48489 : Nat := 24898163455966020264509

theorem tailTrace_48489 : CollatzResearch.WordTrace tailWord_48489 prefixEnd_48489 24898163455966020264509 := by
  unfold tailWord_48489
  simp only [CollatzResearch.WordTrace]
  refine ⟨1768539121340109107004521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1179026080893406071336347 1768539121340109107004521)
  ·
    refine ⟨1326404341005081830253391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1768539121340109107004521 1326404341005081830253391)
    ·
      refine ⟨1989606511507622745380087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1326404341005081830253391 1989606511507622745380087)
      ·
        refine ⟨2984409767261434118070131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1989606511507622745380087 2984409767261434118070131)
        ·
          refine ⟨4476614650892151177105197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2984409767261434118070131 4476614650892151177105197)
          ·
            refine ⟨1678730494084556691414449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4476614650892151177105197 1678730494084556691414449)
            ·
              refine ⟨1259047870563417518560837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1678730494084556691414449 1259047870563417518560837)
              ·
                refine ⟨236071475730640784730157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1259047870563417518560837 236071475730640784730157)
                ·
                  refine ⟨88526803398990294273809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 236071475730640784730157 88526803398990294273809)
                  ·
                    refine ⟨66395102549242720705357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 88526803398990294273809 66395102549242720705357)
                    ·
                      refine ⟨24898163455966020264509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 66395102549242720705357 24898163455966020264509)
                      ·
                        rfl

theorem cell23_48489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 3, 2, 3].length) (baseStart_48489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_48489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_48489 prefixEnd_48489 := by exact prefixLift 48489
  have htrace : WordTrace (prefixWord ++ tailWord_48489) baseStart_48489 baseEnd_48489 := by
    simpa [prefixWord, tailWord_48489, baseEnd_48489] using wordTrace_append hprefix tailTrace_48489
  have hstable : (prefixWord ++ tailWord_48489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48489).length < 2 ^ (prefixWord ++ tailWord_48489).sum := by decide
  have hdescent : baseEnd_48489 < baseStart_48489 := by decide
  rcases family_descends (prefixWord ++ tailWord_48489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48512 : List Nat := [2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 6]
def baseStart_48512 : Nat := 118140960795 + 48512 * 2 ^ 59
def prefixEnd_48512 : Nat := 4983230072969 + 3 ^ 40 * 48512 * 2
def baseEnd_48512 : Nat := 24909973511019430276903

theorem tailTrace_48512 : CollatzResearch.WordTrace tailWord_48512 prefixEnd_48512 24909973511019430276903 := by
  unfold tailWord_48512
  simp only [CollatzResearch.WordTrace]
  refine ⟨884689000128392017545895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1179585333504522690061193 884689000128392017545895)
  ·
    refine ⟨1327033500192588026318843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 884689000128392017545895 1327033500192588026318843)
    ·
      refine ⟨1990550250288882039478265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1327033500192588026318843 1990550250288882039478265)
      ·
        refine ⟨1492912687716661529608699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1990550250288882039478265 1492912687716661529608699)
        ·
          refine ⟨2239369031574992294413049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1492912687716661529608699 2239369031574992294413049)
          ·
            refine ⟨1679526773681244220809787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2239369031574992294413049 1679526773681244220809787)
            ·
              refine ⟨2519290160521866331214681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1679526773681244220809787 2519290160521866331214681)
              ·
                refine ⟨1889467620391399748411011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2519290160521866331214681 1889467620391399748411011)
                ·
                  refine ⟨2834201430587099622616517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1889467620391399748411011 2834201430587099622616517)
                  ·
                    refine ⟨531412768235081179240597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2834201430587099622616517 531412768235081179240597)
                    ·
                      refine ⟨24909973511019430276903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 531412768235081179240597 24909973511019430276903)
                      ·
                        rfl

theorem cell23_48512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 6].length) (baseStart_48512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_48512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_48512 prefixEnd_48512 := by exact prefixLift 48512
  have htrace : WordTrace (prefixWord ++ tailWord_48512) baseStart_48512 baseEnd_48512 := by
    simpa [prefixWord, tailWord_48512, baseEnd_48512] using wordTrace_append hprefix tailTrace_48512
  have hstable : (prefixWord ++ tailWord_48512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48512).length < 2 ^ (prefixWord ++ tailWord_48512).sum := by decide
  have hdescent : baseEnd_48512 < baseStart_48512 := by decide
  rcases family_descends (prefixWord ++ tailWord_48512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48514 : List Nat := [3, 4, 2, 1, 1, 3, 1, 3, 1, 1, 3]
def baseStart_48514 : Nat := 118140960795 + 48514 * 2 ^ 59
def prefixEnd_48514 : Nat := 4983230072969 + 3 ^ 40 * 48514 * 2
def baseEnd_48514 : Nat := 24911000472328422451895

theorem tailTrace_48514 : CollatzResearch.WordTrace tailWord_48514 prefixEnd_48514 24911000472328422451895 := by
  unfold tailWord_48514
  simp only [CollatzResearch.WordTrace]
  refine ⟨442362736562384594166149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1179633964166358917776397 442362736562384594166149)
  ·
    refine ⟨82943013105447111406153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 442362736562384594166149 82943013105447111406153)
    ·
      refine ⟨62207259829085333554615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82943013105447111406153 62207259829085333554615)
      ·
        refine ⟨93310889743628000331923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62207259829085333554615 93310889743628000331923)
        ·
          refine ⟨139966334615442000497885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93310889743628000331923 139966334615442000497885)
          ·
            refine ⟨52487375480790750186707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139966334615442000497885 52487375480790750186707)
            ·
              refine ⟨78731063221186125280061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52487375480790750186707 78731063221186125280061)
              ·
                refine ⟨29524148707944796980023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78731063221186125280061 29524148707944796980023)
                ·
                  refine ⟨44286223061917195470035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29524148707944796980023 44286223061917195470035)
                  ·
                    refine ⟨66429334592875793205053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44286223061917195470035 66429334592875793205053)
                    ·
                      refine ⟨24911000472328422451895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 66429334592875793205053 24911000472328422451895)
                      ·
                        rfl

theorem cell23_48514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_48514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_48514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_48514 prefixEnd_48514 := by exact prefixLift 48514
  have htrace : WordTrace (prefixWord ++ tailWord_48514) baseStart_48514 baseEnd_48514 := by
    simpa [prefixWord, tailWord_48514, baseEnd_48514] using wordTrace_append hprefix tailTrace_48514
  have hstable : (prefixWord ++ tailWord_48514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48514).length < 2 ^ (prefixWord ++ tailWord_48514).sum := by decide
  have hdescent : baseEnd_48514 < baseStart_48514 := by decide
  rcases family_descends (prefixWord ++ tailWord_48514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48526 : List Nat := [4, 1, 1, 4, 2, 2, 9]
def baseStart_48526 : Nat := 118140960795 + 48526 * 2 ^ 59
def prefixEnd_48526 : Nat := 4983230072969 + 3 ^ 40 * 48526 * 2
def baseEnd_48526 : Nat := 307619286915831796319

theorem tailTrace_48526 : CollatzResearch.WordTrace tailWord_48526 prefixEnd_48526 307619286915831796319 := by
  unfold tailWord_48526
  simp only [CollatzResearch.WordTrace]
  refine ⟨221236077775758053262679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1179925748137376284067621 221236077775758053262679)
  ·
    refine ⟨331854116663637079894019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221236077775758053262679 331854116663637079894019)
    ·
      refine ⟨497781174995455619841029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331854116663637079894019 497781174995455619841029)
      ·
        refine ⟨93333970311647928720193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 497781174995455619841029 93333970311647928720193)
        ·
          refine ⟨70000477733735946540145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93333970311647928720193 70000477733735946540145)
          ·
            refine ⟨52500358300301959905109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70000477733735946540145 52500358300301959905109)
            ·
              refine ⟨307619286915831796319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 52500358300301959905109 307619286915831796319)
              ·
                rfl

theorem cell23_48526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 9].length) (baseStart_48526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_48526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_48526 prefixEnd_48526 := by exact prefixLift 48526
  have htrace : WordTrace (prefixWord ++ tailWord_48526) baseStart_48526 baseEnd_48526 := by
    simpa [prefixWord, tailWord_48526, baseEnd_48526] using wordTrace_append hprefix tailTrace_48526
  have hstable : (prefixWord ++ tailWord_48526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48526).length < 2 ^ (prefixWord ++ tailWord_48526).sum := by decide
  have hdescent : baseEnd_48526 < baseStart_48526 := by decide
  rcases family_descends (prefixWord ++ tailWord_48526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48537 : List Nat := [1, 2, 1, 2, 1, 6, 3, 2, 1, 2, 2]
def baseStart_48537 : Nat := 118140960795 + 48537 * 2 ^ 59
def prefixEnd_48537 : Nat := 4983230072969 + 3 ^ 40 * 48537 * 2
def baseEnd_48537 : Nat := 24922810527381832464289

theorem tailTrace_48537 : CollatzResearch.WordTrace tailWord_48537 prefixEnd_48537 24922810527381832464289 := by
  unfold tailWord_48537
  simp only [CollatzResearch.WordTrace]
  refine ⟨1770289825166213304751865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1180193216777475536501243 1770289825166213304751865)
  ·
    refine ⟨1327717368874659978563899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1770289825166213304751865 1327717368874659978563899)
    ·
      refine ⟨1991576053311989967845849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1327717368874659978563899 1991576053311989967845849)
      ·
        refine ⟨1493682039983992475884387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1991576053311989967845849 1493682039983992475884387)
        ·
          refine ⟨2240523059975988713826581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1493682039983992475884387 2240523059975988713826581)
          ·
            refine ⟨105024518436374470960621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 2240523059975988713826581 105024518436374470960621)
            ·
              refine ⟨39384194413640426610233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105024518436374470960621 39384194413640426610233)
              ·
                refine ⟨29538145810230319957675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39384194413640426610233 29538145810230319957675)
                ·
                  refine ⟨44307218715345479936513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29538145810230319957675 44307218715345479936513)
                  ·
                    refine ⟨33230414036509109952385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44307218715345479936513 33230414036509109952385)
                    ·
                      refine ⟨24922810527381832464289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 33230414036509109952385 24922810527381832464289)
                      ·
                        rfl

theorem cell23_48537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 3, 2, 1, 2, 2].length) (baseStart_48537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_48537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_48537 prefixEnd_48537 := by exact prefixLift 48537
  have htrace : WordTrace (prefixWord ++ tailWord_48537) baseStart_48537 baseEnd_48537 := by
    simpa [prefixWord, tailWord_48537, baseEnd_48537] using wordTrace_append hprefix tailTrace_48537
  have hstable : (prefixWord ++ tailWord_48537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48537).length < 2 ^ (prefixWord ++ tailWord_48537).sum := by decide
  have hdescent : baseEnd_48537 < baseStart_48537 := by decide
  rcases family_descends (prefixWord ++ tailWord_48537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48576 : List Nat := [2, 1, 1, 2, 3, 1, 3, 1, 3, 4, 2]
def baseStart_48576 : Nat := 118140960795 + 48576 * 2 ^ 59
def prefixEnd_48576 : Nat := 4983230072969 + 3 ^ 40 * 48576 * 2
def baseEnd_48576 : Nat := 24942836272907179876609

theorem tailTrace_48576 : CollatzResearch.WordTrace tailWord_48576 prefixEnd_48576 24942836272907179876609 := by
  unfold tailWord_48576
  simp only [CollatzResearch.WordTrace]
  refine ⟨885856136012461482710791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1181141514683281976947721 885856136012461482710791)
  ·
    refine ⟨1328784204018692224066187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 885856136012461482710791 1328784204018692224066187)
    ·
      refine ⟨1993176306028038336099281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1328784204018692224066187 1993176306028038336099281)
      ·
        refine ⟨1494882229521028752074461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1993176306028038336099281 1494882229521028752074461)
        ·
          refine ⟨560580836070385782027923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1494882229521028752074461 560580836070385782027923)
          ·
            refine ⟨840871254105578673041885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 560580836070385782027923 840871254105578673041885)
            ·
              refine ⟨315326720289592002390707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 840871254105578673041885 315326720289592002390707)
              ·
                refine ⟨472990080434388003586061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 315326720289592002390707 472990080434388003586061)
                ·
                  refine ⟨177371280162895501344773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 472990080434388003586061 177371280162895501344773)
                  ·
                    refine ⟨33257115030542906502145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 177371280162895501344773 33257115030542906502145)
                    ·
                      refine ⟨24942836272907179876609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 33257115030542906502145 24942836272907179876609)
                      ·
                        rfl

theorem cell23_48576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 3, 4, 2].length) (baseStart_48576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_48576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_48576 prefixEnd_48576 := by exact prefixLift 48576
  have htrace : WordTrace (prefixWord ++ tailWord_48576) baseStart_48576 baseEnd_48576 := by
    simpa [prefixWord, tailWord_48576, baseEnd_48576] using wordTrace_append hprefix tailTrace_48576
  have hstable : (prefixWord ++ tailWord_48576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48576).length < 2 ^ (prefixWord ++ tailWord_48576).sum := by decide
  have hdescent : baseEnd_48576 < baseStart_48576 := by decide
  rcases family_descends (prefixWord ++ tailWord_48576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48579 : List Nat := [1, 1, 1, 3, 1, 1, 6, 1, 2, 1, 5]
def baseStart_48579 : Nat := 118140960795 + 48579 * 2 ^ 59
def prefixEnd_48579 : Nat := 4983230072969 + 3 ^ 40 * 48579 * 2
def baseEnd_48579 : Nat := 24944376714870668139095

theorem tailTrace_48579 : CollatzResearch.WordTrace tailWord_48579 prefixEnd_48579 24944376714870668139095 := by
  unfold tailWord_48579
  simp only [CollatzResearch.WordTrace]
  refine ⟨1771821691014054477780791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1181214460676036318520527 1771821691014054477780791)
  ·
    refine ⟨2657732536521081716671187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1771821691014054477780791 2657732536521081716671187)
    ·
      refine ⟨3986598804781622575006781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2657732536521081716671187 3986598804781622575006781)
      ·
        refine ⟨1494974551793108465627543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3986598804781622575006781 1494974551793108465627543)
        ·
          refine ⟨2242461827689662698441315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1494974551793108465627543 2242461827689662698441315)
          ·
            refine ⟨3363692741534494047661973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2242461827689662698441315 3363692741534494047661973)
            ·
              refine ⟨157673097259429408484155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3363692741534494047661973 157673097259429408484155)
              ·
                refine ⟨236509645889144112726233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157673097259429408484155 236509645889144112726233)
                ·
                  refine ⟨177382234416858084544675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 236509645889144112726233 177382234416858084544675)
                  ·
                    refine ⟨266073351625287126817013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 177382234416858084544675 266073351625287126817013)
                    ·
                      refine ⟨24944376714870668139095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 266073351625287126817013 24944376714870668139095)
                      ·
                        rfl

theorem cell23_48579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 2, 1, 5].length) (baseStart_48579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_48579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_48579 prefixEnd_48579 := by exact prefixLift 48579
  have htrace : WordTrace (prefixWord ++ tailWord_48579) baseStart_48579 baseEnd_48579 := by
    simpa [prefixWord, tailWord_48579, baseEnd_48579] using wordTrace_append hprefix tailTrace_48579
  have hstable : (prefixWord ++ tailWord_48579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48579).length < 2 ^ (prefixWord ++ tailWord_48579).sum := by decide
  have hdescent : baseEnd_48579 < baseStart_48579 := by decide
  rcases family_descends (prefixWord ++ tailWord_48579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48639 : List Nat := [1, 1, 2, 2, 1, 2, 2, 4, 1, 2, 5]
def baseStart_48639 : Nat := 118140960795 + 48639 * 2 ^ 59
def prefixEnd_48639 : Nat := 4983230072969 + 3 ^ 40 * 48639 * 2
def baseEnd_48639 : Nat := 24975185554140433388819

theorem tailTrace_48639 : CollatzResearch.WordTrace tailWord_48639 prefixEnd_48639 24975185554140433388819 := by
  unfold tailWord_48639
  simp only [CollatzResearch.WordTrace]
  refine ⟨1774010070796684724964971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1182673380531123149976647 1774010070796684724964971)
  ·
    refine ⟨2661015106195027087447457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1774010070796684724964971 2661015106195027087447457)
    ·
      refine ⟨1995761329646270315585593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2661015106195027087447457 1995761329646270315585593)
      ·
        refine ⟨1496820997234702736689195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1995761329646270315585593 1496820997234702736689195)
        ·
          refine ⟨2245231495852054105033793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1496820997234702736689195 2245231495852054105033793)
          ·
            refine ⟨1683923621889040578775345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2245231495852054105033793 1683923621889040578775345)
            ·
              refine ⟨1262942716416780434081509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1683923621889040578775345 1262942716416780434081509)
              ·
                refine ⟨236801759328146331390283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1262942716416780434081509 236801759328146331390283)
                ·
                  refine ⟨355202638992219497085425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 236801759328146331390283 355202638992219497085425)
                  ·
                    refine ⟨266401979244164622814069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 355202638992219497085425 266401979244164622814069)
                    ·
                      refine ⟨24975185554140433388819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 266401979244164622814069 24975185554140433388819)
                      ·
                        rfl

theorem cell23_48639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 2, 5].length) (baseStart_48639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_48639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_48639 prefixEnd_48639 := by exact prefixLift 48639
  have htrace : WordTrace (prefixWord ++ tailWord_48639) baseStart_48639 baseEnd_48639 := by
    simpa [prefixWord, tailWord_48639, baseEnd_48639] using wordTrace_append hprefix tailTrace_48639
  have hstable : (prefixWord ++ tailWord_48639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48639).length < 2 ^ (prefixWord ++ tailWord_48639).sum := by decide
  have hdescent : baseEnd_48639 < baseStart_48639 := by decide
  rcases family_descends (prefixWord ++ tailWord_48639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48644 : List Nat := [2, 3, 2, 3, 2, 2, 1, 2, 2, 2, 2]
def baseStart_48644 : Nat := 118140960795 + 48644 * 2 ^ 59
def prefixEnd_48644 : Nat := 4983230072969 + 3 ^ 40 * 48644 * 2
def baseEnd_48644 : Nat := 24977752957412913826297

theorem tailTrace_48644 : CollatzResearch.WordTrace tailWord_48644 prefixEnd_48644 24977752957412913826297 := by
  unfold tailWord_48644
  simp only [CollatzResearch.WordTrace]
  refine ⟨887096217889285289448493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1182794957185713719264657 887096217889285289448493)
  ·
    refine ⟨332661081708481983543185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 887096217889285289448493 332661081708481983543185)
    ·
      refine ⟨249495811281361487657389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332661081708481983543185 249495811281361487657389)
      ·
        refine ⟨93560929230510557871521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249495811281361487657389 93560929230510557871521)
        ·
          refine ⟨70170696922882918403641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93560929230510557871521 70170696922882918403641)
          ·
            refine ⟨52628022692162188802731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70170696922882918403641 52628022692162188802731)
            ·
              refine ⟨78942034038243283204097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52628022692162188802731 78942034038243283204097)
              ·
                refine ⟨59206525528682462403073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78942034038243283204097 59206525528682462403073)
                ·
                  refine ⟨44404894146511846802305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59206525528682462403073 44404894146511846802305)
                  ·
                    refine ⟨33303670609883885101729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44404894146511846802305 33303670609883885101729)
                    ·
                      refine ⟨24977752957412913826297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 33303670609883885101729 24977752957412913826297)
                      ·
                        rfl

theorem cell23_48644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_48644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_48644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_48644 prefixEnd_48644 := by exact prefixLift 48644
  have htrace : WordTrace (prefixWord ++ tailWord_48644) baseStart_48644 baseEnd_48644 := by
    simpa [prefixWord, tailWord_48644, baseEnd_48644] using wordTrace_append hprefix tailTrace_48644
  have hstable : (prefixWord ++ tailWord_48644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48644).length < 2 ^ (prefixWord ++ tailWord_48644).sum := by decide
  have hdescent : baseEnd_48644 < baseStart_48644 := by decide
  rcases family_descends (prefixWord ++ tailWord_48644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48703 : List Nat := [1, 1, 2, 2, 3, 4, 1, 2, 2, 2, 3]
def baseStart_48703 : Nat := 118140960795 + 48703 * 2 ^ 59
def prefixEnd_48703 : Nat := 4983230072969 + 3 ^ 40 * 48703 * 2
def baseEnd_48703 : Nat := 25008048316028182988525

theorem tailTrace_48703 : CollatzResearch.WordTrace tailWord_48703 prefixEnd_48703 25008048316028182988525 := by
  unfold tailWord_48703
  simp only [CollatzResearch.WordTrace]
  refine ⟨1776344342564823655294763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1184229561709882436863175 1776344342564823655294763)
  ·
    refine ⟨2664516513847235482942145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1776344342564823655294763 2664516513847235482942145)
    ·
      refine ⟨1998387385385426612206609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2664516513847235482942145 1998387385385426612206609)
      ·
        refine ⟨1498790539039069959154957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1998387385385426612206609 1498790539039069959154957)
        ·
          refine ⟨562046452139651234683109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1498790539039069959154957 562046452139651234683109)
          ·
            refine ⟨105383709776184606503083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 562046452139651234683109 105383709776184606503083)
            ·
              refine ⟨158075564664276909754625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105383709776184606503083 158075564664276909754625)
              ·
                refine ⟨118556673498207682315969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158075564664276909754625 118556673498207682315969)
                ·
                  refine ⟨88917505123655761736977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118556673498207682315969 88917505123655761736977)
                  ·
                    refine ⟨66688128842741821302733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 88917505123655761736977 66688128842741821302733)
                    ·
                      refine ⟨25008048316028182988525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 66688128842741821302733 25008048316028182988525)
                      ·
                        rfl

theorem cell23_48703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 2, 2, 2, 3].length) (baseStart_48703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_48703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_48703 prefixEnd_48703 := by exact prefixLift 48703
  have htrace : WordTrace (prefixWord ++ tailWord_48703) baseStart_48703 baseEnd_48703 := by
    simpa [prefixWord, tailWord_48703, baseEnd_48703] using wordTrace_append hprefix tailTrace_48703
  have hstable : (prefixWord ++ tailWord_48703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48703).length < 2 ^ (prefixWord ++ tailWord_48703).sum := by decide
  have hdescent : baseEnd_48703 < baseStart_48703 := by decide
  rcases family_descends (prefixWord ++ tailWord_48703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48719 : List Nat := [1, 1, 2, 1, 1, 2, 3, 1, 2, 9]
def baseStart_48719 : Nat := 118140960795 + 48719 * 2 ^ 59
def prefixEnd_48719 : Nat := 4983230072969 + 3 ^ 40 * 48719 * 2
def baseEnd_48719 : Nat := 8338754668833373462817

theorem tailTrace_48719 : CollatzResearch.WordTrace tailWord_48719 prefixEnd_48719 8338754668833373462817 := by
  unfold tailWord_48719
  simp only [CollatzResearch.WordTrace]
  refine ⟨1776927910506858387877211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1184618607004572258584807 1776927910506858387877211)
  ·
    refine ⟨2665391865760287581815817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1776927910506858387877211 2665391865760287581815817)
    ·
      refine ⟨1999043899320215686361863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2665391865760287581815817 1999043899320215686361863)
      ·
        refine ⟨2998565848980323529542795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1999043899320215686361863 2998565848980323529542795)
        ·
          refine ⟨4497848773470485294314193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2998565848980323529542795 4497848773470485294314193)
          ·
            refine ⟨3373386580102863970735645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4497848773470485294314193 3373386580102863970735645)
            ·
              refine ⟨1265019967538573989025867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3373386580102863970735645 1265019967538573989025867)
              ·
                refine ⟨1897529951307860983538801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1265019967538573989025867 1897529951307860983538801)
                ·
                  refine ⟨1423147463480895737654101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1897529951307860983538801 1423147463480895737654101)
                  ·
                    refine ⟨8338754668833373462817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 1423147463480895737654101 8338754668833373462817)
                    ·
                      rfl

theorem cell23_48719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 9].length) (baseStart_48719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_48719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_48719 prefixEnd_48719 := by exact prefixLift 48719
  have htrace : WordTrace (prefixWord ++ tailWord_48719) baseStart_48719 baseEnd_48719 := by
    simpa [prefixWord, tailWord_48719, baseEnd_48719] using wordTrace_append hprefix tailTrace_48719
  have hstable : (prefixWord ++ tailWord_48719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48719).length < 2 ^ (prefixWord ++ tailWord_48719).sum := by decide
  have hdescent : baseEnd_48719 < baseStart_48719 := by decide
  rcases family_descends (prefixWord ++ tailWord_48719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48743 : List Nat := [1, 1, 5, 1, 1, 1, 2, 3, 1, 5, 2]
def baseStart_48743 : Nat := 118140960795 + 48743 * 2 ^ 59
def prefixEnd_48743 : Nat := 4983230072969 + 3 ^ 40 * 48743 * 2
def baseEnd_48743 : Nat := 25028587542208026488341

theorem tailTrace_48743 : CollatzResearch.WordTrace tailWord_48743 prefixEnd_48743 25028587542208026488341 := by
  unfold tailWord_48743
  simp only [CollatzResearch.WordTrace]
  refine ⟨1777803262419910486750883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1185202174946606991167255 1777803262419910486750883)
  ·
    refine ⟨2666704893629865730126325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1777803262419910486750883 2666704893629865730126325)
    ·
      refine ⟨250003583777799912199343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2666704893629865730126325 250003583777799912199343)
      ·
        refine ⟨375005375666699868299015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250003583777799912199343 375005375666699868299015)
        ·
          refine ⟨562508063500049802448523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375005375666699868299015 562508063500049802448523)
          ·
            refine ⟨843762095250074703672785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 562508063500049802448523 843762095250074703672785)
            ·
              refine ⟨632821571437556027754589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 843762095250074703672785 632821571437556027754589)
              ·
                refine ⟨237308089289083510407971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 632821571437556027754589 237308089289083510407971)
                ·
                  refine ⟨355962133933625265611957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 237308089289083510407971 355962133933625265611957)
                  ·
                    refine ⟨33371450056277368651121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 355962133933625265611957 33371450056277368651121)
                    ·
                      refine ⟨25028587542208026488341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 33371450056277368651121 25028587542208026488341)
                      ·
                        rfl

theorem cell23_48743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 5, 2].length) (baseStart_48743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_48743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_48743 prefixEnd_48743 := by exact prefixLift 48743
  have htrace : WordTrace (prefixWord ++ tailWord_48743) baseStart_48743 baseEnd_48743 := by
    simpa [prefixWord, tailWord_48743, baseEnd_48743] using wordTrace_append hprefix tailTrace_48743
  have hstable : (prefixWord ++ tailWord_48743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48743).length < 2 ^ (prefixWord ++ tailWord_48743).sum := by decide
  have hdescent : baseEnd_48743 < baseStart_48743 := by decide
  rcases family_descends (prefixWord ++ tailWord_48743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48896 : List Nat := [2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 9]
def baseStart_48896 : Nat := 118140960795 + 48896 * 2 ^ 59
def prefixEnd_48896 : Nat := 4983230072969 + 3 ^ 40 * 48896 * 2
def baseEnd_48896 : Nat := 25107150082345927875137

theorem tailTrace_48896 : CollatzResearch.WordTrace tailWord_48896 prefixEnd_48896 25107150082345927875137 := by
  unfold tailWord_48896
  simp only [CollatzResearch.WordTrace]
  refine ⟨891691815432808808535271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1188922420577078411380361 891691815432808808535271)
  ·
    refine ⟨1337537723149213212802907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 891691815432808808535271 1337537723149213212802907)
    ·
      refine ⟨2006306584723819819204361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1337537723149213212802907 2006306584723819819204361)
      ·
        refine ⟨1504729938542864864403271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2006306584723819819204361 1504729938542864864403271)
        ·
          refine ⟨2257094907814297296604907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1504729938542864864403271 2257094907814297296604907)
          ·
            refine ⟨3385642361721445944907361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2257094907814297296604907 3385642361721445944907361)
            ·
              refine ⟨2539231771291084458680521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3385642361721445944907361 2539231771291084458680521)
              ·
                refine ⟨1904423828468313344010391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2539231771291084458680521 1904423828468313344010391)
                ·
                  refine ⟨2856635742702470016015587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1904423828468313344010391 2856635742702470016015587)
                  ·
                    refine ⟨4284953614053705024023381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2856635742702470016015587 4284953614053705024023381)
                    ·
                      refine ⟨25107150082345927875137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 4284953614053705024023381 25107150082345927875137)
                      ·
                        rfl

theorem cell23_48896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 9].length) (baseStart_48896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_48896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_48896 prefixEnd_48896 := by exact prefixLift 48896
  have htrace : WordTrace (prefixWord ++ tailWord_48896) baseStart_48896 baseEnd_48896 := by
    simpa [prefixWord, tailWord_48896, baseEnd_48896] using wordTrace_append hprefix tailTrace_48896
  have hstable : (prefixWord ++ tailWord_48896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48896).length < 2 ^ (prefixWord ++ tailWord_48896).sum := by decide
  have hdescent : baseEnd_48896 < baseStart_48896 := by decide
  rcases family_descends (prefixWord ++ tailWord_48896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48913 : List Nat := [1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 3]
def baseStart_48913 : Nat := 118140960795 + 48913 * 2 ^ 59
def prefixEnd_48913 : Nat := 4983230072969 + 3 ^ 40 * 48913 * 2
def baseEnd_48913 : Nat := 25115879253472361362559

theorem tailTrace_48913 : CollatzResearch.WordTrace tailWord_48913 prefixEnd_48913 25115879253472361362559 := by
  unfold tailWord_48913
  simp only [CollatzResearch.WordTrace]
  refine ⟨1784003671804029520439393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1189335781202686346959595 1784003671804029520439393)
  ·
    refine ⟨1338002753853022140329545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1784003671804029520439393 1338002753853022140329545)
    ·
      refine ⟨1003502065389766605247159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1338002753853022140329545 1003502065389766605247159)
      ·
        refine ⟨1505253098084649907870739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1003502065389766605247159 1505253098084649907870739)
        ·
          refine ⟨2257879647126974861806109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1505253098084649907870739 2257879647126974861806109)
          ·
            refine ⟨846704867672615573177291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2257879647126974861806109 846704867672615573177291)
            ·
              refine ⟨1270057301508923359765937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 846704867672615573177291 1270057301508923359765937)
              ·
                refine ⟨952542976131692519824453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1270057301508923359765937 952542976131692519824453)
                ·
                  refine ⟨178601808024692347467085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 952542976131692519824453 178601808024692347467085)
                  ·
                    refine ⟨66975678009259630300157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 178601808024692347467085 66975678009259630300157)
                    ·
                      refine ⟨25115879253472361362559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 66975678009259630300157 25115879253472361362559)
                      ·
                        rfl

theorem cell23_48913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 3].length) (baseStart_48913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_48913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_48913 prefixEnd_48913 := by exact prefixLift 48913
  have htrace : WordTrace (prefixWord ++ tailWord_48913) baseStart_48913 baseEnd_48913 := by
    simpa [prefixWord, tailWord_48913, baseEnd_48913] using wordTrace_append hprefix tailTrace_48913
  have hstable : (prefixWord ++ tailWord_48913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48913).length < 2 ^ (prefixWord ++ tailWord_48913).sum := by decide
  have hdescent : baseEnd_48913 < baseStart_48913 := by decide
  rcases family_descends (prefixWord ++ tailWord_48913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48914 : List Nat := [3, 2, 4, 1, 1, 2, 1, 2, 1, 4, 2]
def baseStart_48914 : Nat := 118140960795 + 48914 * 2 ^ 59
def prefixEnd_48914 : Nat := 4983230072969 + 3 ^ 40 * 48914 * 2
def baseEnd_48914 : Nat := 25116392734126857450055

theorem tailTrace_48914 : CollatzResearch.WordTrace tailWord_48914 prefixEnd_48914 25116392734126857450055 := by
  unfold tailWord_48914
  simp only [CollatzResearch.WordTrace]
  refine ⟨446010036200101672806449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1189360096533604460817197 446010036200101672806449)
  ·
    refine ⟨334507527150076254604837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 446010036200101672806449 334507527150076254604837)
    ·
      refine ⟨62720161340639297738407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 334507527150076254604837 62720161340639297738407)
      ·
        refine ⟨94080242010958946607611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62720161340639297738407 94080242010958946607611)
        ·
          refine ⟨141120363016438419911417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94080242010958946607611 141120363016438419911417)
          ·
            refine ⟨105840272262328814933563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141120363016438419911417 105840272262328814933563)
            ·
              refine ⟨158760408393493222400345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105840272262328814933563 158760408393493222400345)
              ·
                refine ⟨119070306295119916800259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158760408393493222400345 119070306295119916800259)
                ·
                  refine ⟨178605459442679875200389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119070306295119916800259 178605459442679875200389)
                  ·
                    refine ⟨33488523645502476600073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 178605459442679875200389 33488523645502476600073)
                    ·
                      refine ⟨25116392734126857450055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 33488523645502476600073 25116392734126857450055)
                      ·
                        rfl

theorem cell23_48914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_48914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_48914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_48914 prefixEnd_48914 := by exact prefixLift 48914
  have htrace : WordTrace (prefixWord ++ tailWord_48914) baseStart_48914 baseEnd_48914 := by
    simpa [prefixWord, tailWord_48914, baseEnd_48914] using wordTrace_append hprefix tailTrace_48914
  have hstable : (prefixWord ++ tailWord_48914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48914).length < 2 ^ (prefixWord ++ tailWord_48914).sum := by decide
  have hdescent : baseEnd_48914 < baseStart_48914 := by decide
  rcases family_descends (prefixWord ++ tailWord_48914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48930 : List Nat := [3, 3, 1, 1, 2, 1, 2, 2, 2, 3, 3]
def baseStart_48930 : Nat := 118140960795 + 48930 * 2 ^ 59
def prefixEnd_48930 : Nat := 4983230072969 + 3 ^ 40 * 48930 * 2
def baseEnd_48930 : Nat := 25124608424598794849981

theorem tailTrace_48930 : CollatzResearch.WordTrace tailWord_48930 prefixEnd_48930 25124608424598794849981 := by
  unfold tailWord_48930
  simp only [CollatzResearch.WordTrace]
  refine ⟨446155928185610355952061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1189749141828294282538829 446155928185610355952061)
  ·
    refine ⟨167308473069603883482023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 446155928185610355952061 167308473069603883482023)
    ·
      refine ⟨250962709604405825223035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167308473069603883482023 250962709604405825223035)
      ·
        refine ⟨376444064406608737834553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250962709604405825223035 376444064406608737834553)
        ·
          refine ⟨282333048304956553375915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 376444064406608737834553 282333048304956553375915)
          ·
            refine ⟨423499572457434830063873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282333048304956553375915 423499572457434830063873)
            ·
              refine ⟨317624679343076122547905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 423499572457434830063873 317624679343076122547905)
              ·
                refine ⟨238218509507307091910929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 317624679343076122547905 238218509507307091910929)
                ·
                  refine ⟨178663882130480318933197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 238218509507307091910929 178663882130480318933197)
                  ·
                    refine ⟨66998955798930119599949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 178663882130480318933197 66998955798930119599949)
                    ·
                      refine ⟨25124608424598794849981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 66998955798930119599949 25124608424598794849981)
                      ·
                        rfl

theorem cell23_48930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_48930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_48930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_48930 prefixEnd_48930 := by exact prefixLift 48930
  have htrace : WordTrace (prefixWord ++ tailWord_48930) baseStart_48930 baseEnd_48930 := by
    simpa [prefixWord, tailWord_48930, baseEnd_48930] using wordTrace_append hprefix tailTrace_48930
  have hstable : (prefixWord ++ tailWord_48930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48930).length < 2 ^ (prefixWord ++ tailWord_48930).sum := by decide
  have hdescent : baseEnd_48930 < baseStart_48930 := by decide
  rcases family_descends (prefixWord ++ tailWord_48930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48940 : List Nat := [2, 2, 1, 1, 1, 5, 1, 1, 2, 5, 2]
def baseStart_48940 : Nat := 118140960795 + 48940 * 2 ^ 59
def prefixEnd_48940 : Nat := 4983230072969 + 3 ^ 40 * 48940 * 2
def baseEnd_48940 : Nat := 25129743231143755724935

theorem tailTrace_48940 : CollatzResearch.WordTrace tailWord_48940 prefixEnd_48940 25129743231143755724935 := by
  unfold tailWord_48940
  simp only [CollatzResearch.WordTrace]
  refine ⟨892494221353106565836137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1189992295137475421114849 892494221353106565836137)
  ·
    refine ⟨669370666014829924377103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 892494221353106565836137 669370666014829924377103)
    ·
      refine ⟨1004055999022244886565655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 669370666014829924377103 1004055999022244886565655)
      ·
        refine ⟨1506083998533367329848483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1004055999022244886565655 1506083998533367329848483)
        ·
          refine ⟨2259125997800050994772725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1506083998533367329848483 2259125997800050994772725)
          ·
            refine ⟨211793062293754780759943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2259125997800050994772725 211793062293754780759943)
            ·
              refine ⟨317689593440632171139915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211793062293754780759943 317689593440632171139915)
              ·
                refine ⟨476534390160948256709873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 317689593440632171139915 476534390160948256709873)
                ·
                  refine ⟨357400792620711192532405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 476534390160948256709873 357400792620711192532405)
                  ·
                    refine ⟨33506324308191674299913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 357400792620711192532405 33506324308191674299913)
                    ·
                      refine ⟨25129743231143755724935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 33506324308191674299913 25129743231143755724935)
                      ·
                        rfl

theorem cell23_48940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 5, 2].length) (baseStart_48940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_48940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_48940 prefixEnd_48940 := by exact prefixLift 48940
  have htrace : WordTrace (prefixWord ++ tailWord_48940) baseStart_48940 baseEnd_48940 := by
    simpa [prefixWord, tailWord_48940, baseEnd_48940] using wordTrace_append hprefix tailTrace_48940
  have hstable : (prefixWord ++ tailWord_48940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48940).length < 2 ^ (prefixWord ++ tailWord_48940).sum := by decide
  have hdescent : baseEnd_48940 < baseStart_48940 := by decide
  rcases family_descends (prefixWord ++ tailWord_48940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48970 : List Nat := [3, 1, 2, 1, 1, 1, 3, 2, 1, 6, 2]
def baseStart_48970 : Nat := 118140960795 + 48970 * 2 ^ 59
def prefixEnd_48970 : Nat := 4983230072969 + 3 ^ 40 * 48970 * 2
def baseEnd_48970 : Nat := 25145147650778638349797

theorem tailTrace_48970 : CollatzResearch.WordTrace tailWord_48970 prefixEnd_48970 25145147650778638349797 := by
  unfold tailWord_48970
  simp only [CollatzResearch.WordTrace]
  refine ⟨446520658149382063816091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1190721755065018836842909 446520658149382063816091)
  ·
    refine ⟨669780987224073095724137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 446520658149382063816091 669780987224073095724137)
    ·
      refine ⟨502335740418054821793103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 669780987224073095724137 502335740418054821793103)
      ·
        refine ⟨753503610627082232689655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 502335740418054821793103 753503610627082232689655)
        ·
          refine ⟨1130255415940623349034483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 753503610627082232689655 1130255415940623349034483)
          ·
            refine ⟨1695383123910935023551725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1130255415940623349034483 1695383123910935023551725)
            ·
              refine ⟨635768671466600633831897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1695383123910935023551725 635768671466600633831897)
              ·
                refine ⟨476826503599950475373923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 635768671466600633831897 476826503599950475373923)
                ·
                  refine ⟨715239755399925713060885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 476826503599950475373923 715239755399925713060885)
                  ·
                    refine ⟨33526863534371517799729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 715239755399925713060885 33526863534371517799729)
                    ·
                      refine ⟨25145147650778638349797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 33526863534371517799729 25145147650778638349797)
                      ·
                        rfl

theorem cell23_48970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 1, 6, 2].length) (baseStart_48970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_48970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_48970 prefixEnd_48970 := by exact prefixLift 48970
  have htrace : WordTrace (prefixWord ++ tailWord_48970) baseStart_48970 baseEnd_48970 := by
    simpa [prefixWord, tailWord_48970, baseEnd_48970] using wordTrace_append hprefix tailTrace_48970
  have hstable : (prefixWord ++ tailWord_48970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48970).length < 2 ^ (prefixWord ++ tailWord_48970).sum := by decide
  have hdescent : baseEnd_48970 < baseStart_48970 := by decide
  rcases family_descends (prefixWord ++ tailWord_48970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48993 : List Nat := [1, 2, 3, 1, 1, 1, 5, 1, 8]
def baseStart_48993 : Nat := 118140960795 + 48993 * 2 ^ 59
def prefixEnd_48993 : Nat := 4983230072969 + 3 ^ 40 * 48993 * 2
def baseEnd_48993 : Nat := 2795217522870227595799

theorem tailTrace_48993 : CollatzResearch.WordTrace tailWord_48993 prefixEnd_48993 2795217522870227595799 := by
  unfold tailWord_48993
  simp only [CollatzResearch.WordTrace]
  refine ⟨1786921511514203183351633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1191281007676135455567755 1786921511514203183351633)
  ·
    refine ⟨1340191133635652387513725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1786921511514203183351633 1340191133635652387513725)
    ·
      refine ⟨502571675113369645317647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1340191133635652387513725 502571675113369645317647)
      ·
        refine ⟨753857512670054467976471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 502571675113369645317647 753857512670054467976471)
        ·
          refine ⟨1130786269005081701964707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 753857512670054467976471 1130786269005081701964707)
          ·
            refine ⟨1696179403507622552947061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1130786269005081701964707 1696179403507622552947061)
            ·
              refine ⟨159016819078839614338787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1696179403507622552947061 159016819078839614338787)
              ·
                refine ⟨238525228618259421508181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159016819078839614338787 238525228618259421508181)
                ·
                  refine ⟨2795217522870227595799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 238525228618259421508181 2795217522870227595799)
                  ·
                    rfl

theorem cell23_48993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 8].length) (baseStart_48993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_48993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_48993 prefixEnd_48993 := by exact prefixLift 48993
  have htrace : WordTrace (prefixWord ++ tailWord_48993) baseStart_48993 baseEnd_48993 := by
    simpa [prefixWord, tailWord_48993, baseEnd_48993] using wordTrace_append hprefix tailTrace_48993
  have hstable : (prefixWord ++ tailWord_48993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48993).length < 2 ^ (prefixWord ++ tailWord_48993).sum := by decide
  have hdescent : baseEnd_48993 < baseStart_48993 := by decide
  rcases family_descends (prefixWord ++ tailWord_48993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49031 : List Nat := [1, 1, 4, 2, 4, 2, 1, 3, 1, 4]
def baseStart_49031 : Nat := 118140960795 + 49031 * 2 ^ 59
def prefixEnd_49031 : Nat := 4983230072969 + 3 ^ 40 * 49031 * 2
def baseEnd_49031 : Nat := 8392156656900966562339

theorem tailTrace_49031 : CollatzResearch.WordTrace tailWord_49031 prefixEnd_49031 8392156656900966562339 := by
  unfold tailWord_49031
  simp only [CollatzResearch.WordTrace]
  refine ⟨1788307485376535673234947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1192204990251023782156631 1788307485376535673234947)
  ·
    refine ⟨2682461228064803509852421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1788307485376535673234947 2682461228064803509852421)
    ·
      refine ⟨502961480262150658097329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2682461228064803509852421 502961480262150658097329)
      ·
        refine ⟨377221110196612993572997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 502961480262150658097329 377221110196612993572997)
        ·
          refine ⟨70728958161864936294937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 377221110196612993572997 70728958161864936294937)
          ·
            refine ⟨53046718621398702221203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70728958161864936294937 53046718621398702221203)
            ·
              refine ⟨79570077932098053331805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53046718621398702221203 79570077932098053331805)
              ·
                refine ⟨29838779224536769999427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79570077932098053331805 29838779224536769999427)
                ·
                  refine ⟨44758168836805154999141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29838779224536769999427 44758168836805154999141)
                  ·
                    refine ⟨8392156656900966562339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44758168836805154999141 8392156656900966562339)
                    ·
                      rfl

theorem cell23_49031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 3, 1, 4].length) (baseStart_49031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_49031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_49031 prefixEnd_49031 := by exact prefixLift 49031
  have htrace : WordTrace (prefixWord ++ tailWord_49031) baseStart_49031 baseEnd_49031 := by
    simpa [prefixWord, tailWord_49031, baseEnd_49031] using wordTrace_append hprefix tailTrace_49031
  have hstable : (prefixWord ++ tailWord_49031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49031).length < 2 ^ (prefixWord ++ tailWord_49031).sum := by decide
  have hdescent : baseEnd_49031 < baseStart_49031 := by decide
  rcases family_descends (prefixWord ++ tailWord_49031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49043 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 1, 7, 4]
def baseStart_49043 : Nat := 118140960795 + 49043 * 2 ^ 59
def prefixEnd_49043 : Nat := 4983230072969 + 3 ^ 40 * 49043 * 2
def baseEnd_49043 : Nat := 25182631738556852736961

theorem tailTrace_49043 : CollatzResearch.WordTrace tailWord_49043 prefixEnd_49043 25182631738556852736961 := by
  unfold tailWord_49043
  simp only [CollatzResearch.WordTrace]
  refine ⟨1788745161333061722671783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1192496774222041148447855 1788745161333061722671783)
  ·
    refine ⟨2683117741999592584007675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1788745161333061722671783 2683117741999592584007675)
    ·
      refine ⟨4024676612999388876011513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2683117741999592584007675 4024676612999388876011513)
      ·
        refine ⟨3018507459749541657008635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4024676612999388876011513 3018507459749541657008635)
        ·
          refine ⟨4527761189624312485512953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3018507459749541657008635 4527761189624312485512953)
          ·
            refine ⟨3395820892218234364134715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4527761189624312485512953 3395820892218234364134715)
            ·
              refine ⟨5093731338327351546202073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3395820892218234364134715 5093731338327351546202073)
              ·
                refine ⟨3820298503745513659651555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5093731338327351546202073 3820298503745513659651555)
                ·
                  refine ⟨5730447755618270489477333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3820298503745513659651555 5730447755618270489477333)
                  ·
                    refine ⟨134307369272303214597125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5730447755618270489477333 134307369272303214597125)
                    ·
                      refine ⟨25182631738556852736961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 134307369272303214597125 25182631738556852736961)
                      ·
                        rfl

theorem cell23_49043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 7, 4].length) (baseStart_49043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_49043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_49043 prefixEnd_49043 := by exact prefixLift 49043
  have htrace : WordTrace (prefixWord ++ tailWord_49043) baseStart_49043 baseEnd_49043 := by
    simpa [prefixWord, tailWord_49043, baseEnd_49043] using wordTrace_append hprefix tailTrace_49043
  have hstable : (prefixWord ++ tailWord_49043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49043).length < 2 ^ (prefixWord ++ tailWord_49043).sum := by decide
  have hdescent : baseEnd_49043 < baseStart_49043 := by decide
  rcases family_descends (prefixWord ++ tailWord_49043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49047 : List Nat := [1, 1, 3, 3, 1, 3, 1, 1, 4, 3, 2]
def baseStart_49047 : Nat := 118140960795 + 49047 * 2 ^ 59
def prefixEnd_49047 : Nat := 4983230072969 + 3 ^ 40 * 49047 * 2
def baseEnd_49047 : Nat := 25184685661174837086943

theorem tailTrace_49047 : CollatzResearch.WordTrace tailWord_49047 prefixEnd_49047 25184685661174837086943 := by
  unfold tailWord_49047
  simp only [CollatzResearch.WordTrace]
  refine ⟨1788891053318570405817395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1192594035545713603878263 1788891053318570405817395)
  ·
    refine ⟨2683336579977855608726093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1788891053318570405817395 2683336579977855608726093)
    ·
      refine ⟨1006251217491695853272285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2683336579977855608726093 1006251217491695853272285)
      ·
        refine ⟨377344206559385944977107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1006251217491695853272285 377344206559385944977107)
        ·
          refine ⟨566016309839078917465661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 377344206559385944977107 566016309839078917465661)
          ·
            refine ⟨212256116189654594049623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 566016309839078917465661 212256116189654594049623)
            ·
              refine ⟨318384174284481891074435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212256116189654594049623 318384174284481891074435)
              ·
                refine ⟨477576261426722836611653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 318384174284481891074435 477576261426722836611653)
                ·
                  refine ⟨89545549017510531864685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 477576261426722836611653 89545549017510531864685)
                  ·
                    refine ⟨33579580881566449449257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 89545549017510531864685 33579580881566449449257)
                    ·
                      refine ⟨25184685661174837086943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 33579580881566449449257 25184685661174837086943)
                      ·
                        rfl

theorem cell23_49047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 4, 3, 2].length) (baseStart_49047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_49047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_49047 prefixEnd_49047 := by exact prefixLift 49047
  have htrace : WordTrace (prefixWord ++ tailWord_49047) baseStart_49047 baseEnd_49047 := by
    simpa [prefixWord, tailWord_49047, baseEnd_49047] using wordTrace_append hprefix tailTrace_49047
  have hstable : (prefixWord ++ tailWord_49047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49047).length < 2 ^ (prefixWord ++ tailWord_49047).sum := by decide
  have hdescent : baseEnd_49047 < baseStart_49047 := by decide
  rcases family_descends (prefixWord ++ tailWord_49047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49048 : List Nat := [2, 1, 2, 6, 1, 1, 3, 2, 1, 4]
def baseStart_49048 : Nat := 118140960795 + 49048 * 2 ^ 59
def prefixEnd_49048 : Nat := 4983230072969 + 3 ^ 40 * 49048 * 2
def baseEnd_49048 : Nat := 8395066380609777724813

theorem tailTrace_49048 : CollatzResearch.WordTrace tailWord_49048 prefixEnd_49048 8395066380609777724813 := by
  unfold tailWord_49048
  simp only [CollatzResearch.WordTrace]
  refine ⟨894463763157473788301899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1192618350876631717735865 894463763157473788301899)
  ·
    refine ⟨1341695644736210682452849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 894463763157473788301899 1341695644736210682452849)
    ·
      refine ⟨1006271733552158011839637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1341695644736210682452849 1006271733552158011839637)
      ·
        refine ⟨47168987510257406804983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 1006271733552158011839637 47168987510257406804983)
        ·
          refine ⟨70753481265386110207475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47168987510257406804983 70753481265386110207475)
          ·
            refine ⟨106130221898079165311213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70753481265386110207475 106130221898079165311213)
            ·
              refine ⟨39798833211779686991705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106130221898079165311213 39798833211779686991705)
              ·
                refine ⟨29849124908834765243779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39798833211779686991705 29849124908834765243779)
                ·
                  refine ⟨44773687363252147865669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29849124908834765243779 44773687363252147865669)
                  ·
                    refine ⟨8395066380609777724813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44773687363252147865669 8395066380609777724813)
                    ·
                      rfl

theorem cell23_49048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 3, 2, 1, 4].length) (baseStart_49048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_49048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_49048 prefixEnd_49048 := by exact prefixLift 49048
  have htrace : WordTrace (prefixWord ++ tailWord_49048) baseStart_49048 baseEnd_49048 := by
    simpa [prefixWord, tailWord_49048, baseEnd_49048] using wordTrace_append hprefix tailTrace_49048
  have hstable : (prefixWord ++ tailWord_49048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49048).length < 2 ^ (prefixWord ++ tailWord_49048).sum := by decide
  have hdescent : baseEnd_49048 < baseStart_49048 := by decide
  rcases family_descends (prefixWord ++ tailWord_49048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49077 : List Nat := [1, 3, 3, 2, 1, 3, 1, 1, 3, 1, 4]
def baseStart_49077 : Nat := 118140960795 + 49077 * 2 ^ 59
def prefixEnd_49077 : Nat := 4983230072969 + 3 ^ 40 * 49077 * 2
def baseEnd_49077 : Nat := 25200090080809719711805

theorem tailTrace_49077 : CollatzResearch.WordTrace tailWord_49077 prefixEnd_49077 25200090080809719711805 := by
  unfold tailWord_49077
  simp only [CollatzResearch.WordTrace]
  refine ⟨1789985243209885529409485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1193323495473257019606323 1789985243209885529409485)
  ·
    refine ⟨671244466203707073528557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1789985243209885529409485 671244466203707073528557)
    ·
      refine ⟨251716674826390152573209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 671244466203707073528557 251716674826390152573209)
      ·
        refine ⟨188787506119792614429907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251716674826390152573209 188787506119792614429907)
        ·
          refine ⟨283181259179688921644861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188787506119792614429907 283181259179688921644861)
          ·
            refine ⟨106192972192383345616823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 283181259179688921644861 106192972192383345616823)
            ·
              refine ⟨159289458288575018425235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106192972192383345616823 159289458288575018425235)
              ·
                refine ⟨238934187432862527637853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159289458288575018425235 238934187432862527637853)
                ·
                  refine ⟨89600320287323447864195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 238934187432862527637853 89600320287323447864195)
                  ·
                    refine ⟨134400480430985171796293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 89600320287323447864195 134400480430985171796293)
                    ·
                      refine ⟨25200090080809719711805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 134400480430985171796293 25200090080809719711805)
                      ·
                        rfl

theorem cell23_49077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_49077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_49077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_49077 prefixEnd_49077 := by exact prefixLift 49077
  have htrace : WordTrace (prefixWord ++ tailWord_49077) baseStart_49077 baseEnd_49077 := by
    simpa [prefixWord, tailWord_49077, baseEnd_49077] using wordTrace_append hprefix tailTrace_49077
  have hstable : (prefixWord ++ tailWord_49077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49077).length < 2 ^ (prefixWord ++ tailWord_49077).sum := by decide
  have hdescent : baseEnd_49077 < baseStart_49077 := by decide
  rcases family_descends (prefixWord ++ tailWord_49077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49111 : List Nat := [1, 1, 3, 2, 1, 1, 5, 4, 1, 2, 2]
def baseStart_49111 : Nat := 118140960795 + 49111 * 2 ^ 59
def prefixEnd_49111 : Nat := 4983230072969 + 3 ^ 40 * 49111 * 2
def baseEnd_49111 : Nat := 25217548423062586686649

theorem tailTrace_49111 : CollatzResearch.WordTrace tailWord_49111 prefixEnd_49111 25217548423062586686649 := by
  unfold tailWord_49111
  simp only [CollatzResearch.WordTrace]
  refine ⟨1791225325086709336147187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1194150216724472890764791 1791225325086709336147187)
  ·
    refine ⟨2686837987630064004220781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1791225325086709336147187 2686837987630064004220781)
    ·
      refine ⟨1007564245361274001582793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2686837987630064004220781 1007564245361274001582793)
      ·
        refine ⟨755673184020955501187095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1007564245361274001582793 755673184020955501187095)
        ·
          refine ⟨1133509776031433251780643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 755673184020955501187095 1133509776031433251780643)
          ·
            refine ⟨1700264664047149877670965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1133509776031433251780643 1700264664047149877670965)
            ·
              refine ⟨159399812254420301031653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1700264664047149877670965 159399812254420301031653)
              ·
                refine ⟨29887464797703806443435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 159399812254420301031653 29887464797703806443435)
                ·
                  refine ⟨44831197196555709665153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29887464797703806443435 44831197196555709665153)
                  ·
                    refine ⟨33623397897416782248865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44831197196555709665153 33623397897416782248865)
                    ·
                      refine ⟨25217548423062586686649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 33623397897416782248865 25217548423062586686649)
                      ·
                        rfl

theorem cell23_49111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 4, 1, 2, 2].length) (baseStart_49111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_49111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_49111 prefixEnd_49111 := by exact prefixLift 49111
  have htrace : WordTrace (prefixWord ++ tailWord_49111) baseStart_49111 baseEnd_49111 := by
    simpa [prefixWord, tailWord_49111, baseEnd_49111] using wordTrace_append hprefix tailTrace_49111
  have hstable : (prefixWord ++ tailWord_49111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49111).length < 2 ^ (prefixWord ++ tailWord_49111).sum := by decide
  have hdescent : baseEnd_49111 < baseStart_49111 := by decide
  rcases family_descends (prefixWord ++ tailWord_49111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49130 : List Nat := [3, 1, 3, 1, 2, 1, 1, 2, 2, 7]
def baseStart_49130 : Nat := 118140960795 + 49130 * 2 ^ 59
def prefixEnd_49130 : Nat := 4983230072969 + 3 ^ 40 * 49130 * 2
def baseEnd_49130 : Nat := 8409101518499337449687

theorem tailTrace_49130 : CollatzResearch.WordTrace tailWord_49130 prefixEnd_49130 8409101518499337449687 := by
  unfold tailWord_49130
  simp only [CollatzResearch.WordTrace]
  refine ⟨447979578004468895272211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1194612208011917054059229 447979578004468895272211)
  ·
    refine ⟨671969367006703342908317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 447979578004468895272211 671969367006703342908317)
    ·
      refine ⟨251988512627513753590619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 671969367006703342908317 251988512627513753590619)
      ·
        refine ⟨377982768941270630385929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251988512627513753590619 377982768941270630385929)
        ·
          refine ⟨283487076705952972789447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 377982768941270630385929 283487076705952972789447)
          ·
            refine ⟨425230615058929459184171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283487076705952972789447 425230615058929459184171)
            ·
              refine ⟨637845922588394188776257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 425230615058929459184171 637845922588394188776257)
              ·
                refine ⟨478384441941295641582193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 637845922588394188776257 478384441941295641582193)
                ·
                  refine ⟨358788331455971731186645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 478384441941295641582193 358788331455971731186645)
                  ·
                    refine ⟨8409101518499337449687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 358788331455971731186645 8409101518499337449687)
                    ·
                      rfl

theorem cell23_49130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_49130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_49130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_49130 prefixEnd_49130 := by exact prefixLift 49130
  have htrace : WordTrace (prefixWord ++ tailWord_49130) baseStart_49130 baseEnd_49130 := by
    simpa [prefixWord, tailWord_49130, baseEnd_49130] using wordTrace_append hprefix tailTrace_49130
  have hstable : (prefixWord ++ tailWord_49130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49130).length < 2 ^ (prefixWord ++ tailWord_49130).sum := by decide
  have hdescent : baseEnd_49130 < baseStart_49130 := by decide
  rcases family_descends (prefixWord ++ tailWord_49130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49160 : List Nat := [2, 1, 3, 2, 1, 2, 1, 1, 4, 6]
def baseStart_49160 : Nat := 118140960795 + 49160 * 2 ^ 59
def prefixEnd_49160 : Nat := 4983230072969 + 3 ^ 40 * 49160 * 2
def baseEnd_49160 : Nat := 8414236325044298324641

theorem tailTrace_49160 : CollatzResearch.WordTrace tailWord_49160 prefixEnd_49160 8414236325044298324641 := by
  unfold tailWord_49160
  simp only [CollatzResearch.WordTrace]
  refine ⟨896506250954595352340467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1195341667939460469787289 896506250954595352340467)
  ·
    refine ⟨1344759376431893028510701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 896506250954595352340467 1344759376431893028510701)
    ·
      refine ⟨504284766161959885691513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1344759376431893028510701 504284766161959885691513)
      ·
        refine ⟨378213574621469914268635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 504284766161959885691513 378213574621469914268635)
        ·
          refine ⟨567320361932204871402953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 378213574621469914268635 567320361932204871402953)
          ·
            refine ⟨425490271449153653552215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 567320361932204871402953 425490271449153653552215)
            ·
              refine ⟨638235407173730480328323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 425490271449153653552215 638235407173730480328323)
              ·
                refine ⟨957353110760595720492485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 638235407173730480328323 957353110760595720492485)
                ·
                  refine ⟨179503708267611697592341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 957353110760595720492485 179503708267611697592341)
                  ·
                    refine ⟨8414236325044298324641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 179503708267611697592341 8414236325044298324641)
                    ·
                      rfl

theorem cell23_49160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 4, 6].length) (baseStart_49160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_49160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_49160 prefixEnd_49160 := by exact prefixLift 49160
  have htrace : WordTrace (prefixWord ++ tailWord_49160) baseStart_49160 baseEnd_49160 := by
    simpa [prefixWord, tailWord_49160, baseEnd_49160] using wordTrace_append hprefix tailTrace_49160
  have hstable : (prefixWord ++ tailWord_49160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49160).length < 2 ^ (prefixWord ++ tailWord_49160).sum := by decide
  have hdescent : baseEnd_49160 < baseStart_49160 := by decide
  rcases family_descends (prefixWord ++ tailWord_49160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49188 : List Nat := [2, 3, 1, 4, 2, 1, 2, 2, 1, 3, 2]
def baseStart_49188 : Nat := 118140960795 + 49188 * 2 ^ 59
def prefixEnd_49188 : Nat := 4983230072969 + 3 ^ 40 * 49188 * 2
def baseEnd_49188 : Nat := 25257086433458785423795

theorem tailTrace_49188 : CollatzResearch.WordTrace tailWord_49188 prefixEnd_49188 25257086433458785423795 := by
  unfold tailWord_49188
  simp only [CollatzResearch.WordTrace]
  refine ⟨897016872903875743350109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1196022497205167657800145 897016872903875743350109)
  ·
    refine ⟨336381327338953403756291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 897016872903875743350109 336381327338953403756291)
    ·
      refine ⟨504571991008430105634437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336381327338953403756291 504571991008430105634437)
      ·
        refine ⟨94607248314080644806457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 504571991008430105634437 94607248314080644806457)
        ·
          refine ⟨70955436235560483604843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94607248314080644806457 70955436235560483604843)
          ·
            refine ⟨106433154353340725407265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70955436235560483604843 106433154353340725407265)
            ·
              refine ⟨79824865765005544055449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106433154353340725407265 79824865765005544055449)
              ·
                refine ⟨59868649323754158041587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79824865765005544055449 59868649323754158041587)
                ·
                  refine ⟨89802973985631237062381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59868649323754158041587 89802973985631237062381)
                  ·
                    refine ⟨33676115244611713898393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 89802973985631237062381 33676115244611713898393)
                    ·
                      refine ⟨25257086433458785423795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 33676115244611713898393 25257086433458785423795)
                      ·
                        rfl

theorem cell23_49188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_49188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_49188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_49188 prefixEnd_49188 := by exact prefixLift 49188
  have htrace : WordTrace (prefixWord ++ tailWord_49188) baseStart_49188 baseEnd_49188 := by
    simpa [prefixWord, tailWord_49188, baseEnd_49188] using wordTrace_append hprefix tailTrace_49188
  have hstable : (prefixWord ++ tailWord_49188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49188).length < 2 ^ (prefixWord ++ tailWord_49188).sum := by decide
  have hdescent : baseEnd_49188 < baseStart_49188 := by decide
  rcases family_descends (prefixWord ++ tailWord_49188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49227 : List Nat := [1, 1, 1, 1, 3, 1, 2, 3, 1, 7, 2]
def baseStart_49227 : Nat := 118140960795 + 49227 * 2 ^ 59
def prefixEnd_49227 : Nat := 4983230072969 + 3 ^ 40 * 49227 * 2
def baseEnd_49227 : Nat := 25277112178984132836115

theorem tailTrace_49227 : CollatzResearch.WordTrace tailWord_49227 prefixEnd_49227 25277112178984132836115 := by
  unfold tailWord_49227
  simp only [CollatzResearch.WordTrace]
  refine ⟨1795456192666461147369935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1196970795110974098246623 1795456192666461147369935)
  ·
    refine ⟨2693184288999691721054903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1795456192666461147369935 2693184288999691721054903)
    ·
      refine ⟨4039776433499537581582355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2693184288999691721054903 4039776433499537581582355)
      ·
        refine ⟨6059664650249306372373533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4039776433499537581582355 6059664650249306372373533)
        ·
          refine ⟨2272374243843489889640075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6059664650249306372373533 2272374243843489889640075)
          ·
            refine ⟨3408561365765234834460113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2272374243843489889640075 3408561365765234834460113)
            ·
              refine ⟨2556421024323926125845085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3408561365765234834460113 2556421024323926125845085)
              ·
                refine ⟨958657884121472297191907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2556421024323926125845085 958657884121472297191907)
                ·
                  refine ⟨1437986826182208445787861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 958657884121472297191907 1437986826182208445787861)
                  ·
                    refine ⟨33702816238645510448153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1437986826182208445787861 33702816238645510448153)
                    ·
                      refine ⟨25277112178984132836115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 33702816238645510448153 25277112178984132836115)
                      ·
                        rfl

theorem cell23_49227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 7, 2].length) (baseStart_49227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_49227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_49227 prefixEnd_49227 := by exact prefixLift 49227
  have htrace : WordTrace (prefixWord ++ tailWord_49227) baseStart_49227 baseEnd_49227 := by
    simpa [prefixWord, tailWord_49227, baseEnd_49227] using wordTrace_append hprefix tailTrace_49227
  have hstable : (prefixWord ++ tailWord_49227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49227).length < 2 ^ (prefixWord ++ tailWord_49227).sum := by decide
  have hdescent : baseEnd_49227 < baseStart_49227 := by decide
  rcases family_descends (prefixWord ++ tailWord_49227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49284 : List Nat := [2, 3, 2, 1, 2, 1, 2, 3, 3, 4]
def baseStart_49284 : Nat := 118140960795 + 49284 * 2 ^ 59
def prefixEnd_49284 : Nat := 4983230072969 + 3 ^ 40 * 49284 * 2
def baseEnd_49284 : Nat := 8435460192096803274451

theorem tailTrace_49284 : CollatzResearch.WordTrace tailWord_49284 prefixEnd_49284 8435460192096803274451 := by
  unfold tailWord_49284
  simp only [CollatzResearch.WordTrace]
  refine ⟨898767576729979941097453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1198356768973306588129937 898767576729979941097453)
  ·
    refine ⟨337037841273742477911545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 898767576729979941097453 337037841273742477911545)
    ·
      refine ⟨252778380955306858433659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 337037841273742477911545 252778380955306858433659)
      ·
        refine ⟨379167571432960287650489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252778380955306858433659 379167571432960287650489)
        ·
          refine ⟨284375678574720215737867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 379167571432960287650489 284375678574720215737867)
          ·
            refine ⟨426563517862080323606801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284375678574720215737867 426563517862080323606801)
            ·
              refine ⟨319922638396560242705101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 426563517862080323606801 319922638396560242705101)
              ·
                refine ⟨119970989398710091014413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 319922638396560242705101 119970989398710091014413)
                ·
                  refine ⟨44989121024516284130405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 119970989398710091014413 44989121024516284130405)
                  ·
                    refine ⟨8435460192096803274451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44989121024516284130405 8435460192096803274451)
                    ·
                      rfl

theorem cell23_49284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_49284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_49284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_49284 prefixEnd_49284 := by exact prefixLift 49284
  have htrace : WordTrace (prefixWord ++ tailWord_49284) baseStart_49284 baseEnd_49284 := by
    simpa [prefixWord, tailWord_49284, baseEnd_49284] using wordTrace_append hprefix tailTrace_49284
  have hstable : (prefixWord ++ tailWord_49284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49284).length < 2 ^ (prefixWord ++ tailWord_49284).sum := by decide
  have hdescent : baseEnd_49284 < baseStart_49284 := by decide
  rcases family_descends (prefixWord ++ tailWord_49284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49311 : List Nat := [1, 1, 2, 6, 1, 1, 3, 1, 2, 2, 3]
def baseStart_49311 : Nat := 118140960795 + 49311 * 2 ^ 59
def prefixEnd_49311 : Nat := 4983230072969 + 3 ^ 40 * 49311 * 2
def baseEnd_49311 : Nat := 25320244553961804185729

theorem tailTrace_49311 : CollatzResearch.WordTrace tailWord_49311 prefixEnd_49311 25320244553961804185729 := by
  unfold tailWord_49311
  simp only [CollatzResearch.WordTrace]
  refine ⟨1798519924362143493427787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1199013282908095662285191 1798519924362143493427787)
  ·
    refine ⟨2697779886543215240141681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1798519924362143493427787 2697779886543215240141681)
    ·
      refine ⟨2023334914907411430106261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2697779886543215240141681 2023334914907411430106261)
      ·
        refine ⟨94843824136284910786231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 2023334914907411430106261 94843824136284910786231)
        ·
          refine ⟨142265736204427366179347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94843824136284910786231 142265736204427366179347)
          ·
            refine ⟨213398604306641049269021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142265736204427366179347 213398604306641049269021)
            ·
              refine ⟨80024476614990393475883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 213398604306641049269021 80024476614990393475883)
              ·
                refine ⟨120036714922485590213825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80024476614990393475883 120036714922485590213825)
                ·
                  refine ⟨90027536191864192660369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120036714922485590213825 90027536191864192660369)
                  ·
                    refine ⟨67520652143898144495277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 90027536191864192660369 67520652143898144495277)
                    ·
                      refine ⟨25320244553961804185729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 67520652143898144495277 25320244553961804185729)
                      ·
                        rfl

theorem cell23_49311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_49311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_49311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_49311 prefixEnd_49311 := by exact prefixLift 49311
  have htrace : WordTrace (prefixWord ++ tailWord_49311) baseStart_49311 baseEnd_49311 := by
    simpa [prefixWord, tailWord_49311, baseEnd_49311] using wordTrace_append hprefix tailTrace_49311
  have hstable : (prefixWord ++ tailWord_49311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49311).length < 2 ^ (prefixWord ++ tailWord_49311).sum := by decide
  have hdescent : baseEnd_49311 < baseStart_49311 := by decide
  rcases family_descends (prefixWord ++ tailWord_49311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49367 : List Nat := [1, 1, 3, 2, 1, 2, 1, 1, 5, 1, 5]
def baseStart_49367 : Nat := 118140960795 + 49367 * 2 ^ 59
def prefixEnd_49367 : Nat := 4983230072969 + 3 ^ 40 * 49367 * 2
def baseEnd_49367 : Nat := 25348999470613585085471

theorem tailTrace_49367 : CollatzResearch.WordTrace tailWord_49367 prefixEnd_49367 25348999470613585085471 := by
  unfold tailWord_49367
  simp only [CollatzResearch.WordTrace]
  refine ⟨1800562412159265057466355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1200374941439510038310903 1800562412159265057466355)
  ·
    refine ⟨2700843618238897586199533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1800562412159265057466355 2700843618238897586199533)
    ·
      refine ⟨1012816356839586594824825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2700843618238897586199533 1012816356839586594824825)
      ·
        refine ⟨759612267629689946118619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1012816356839586594824825 759612267629689946118619)
        ·
          refine ⟨1139418401444534919177929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 759612267629689946118619 1139418401444534919177929)
          ·
            refine ⟨854563801083401189383447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1139418401444534919177929 854563801083401189383447)
            ·
              refine ⟨1281845701625101784075171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 854563801083401189383447 1281845701625101784075171)
              ·
                refine ⟨1922768552437652676112757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1281845701625101784075171 1922768552437652676112757)
                ·
                  refine ⟨180259551791029938385571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1922768552437652676112757 180259551791029938385571)
                  ·
                    refine ⟨270389327686544907578357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 180259551791029938385571 270389327686544907578357)
                    ·
                      refine ⟨25348999470613585085471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 270389327686544907578357 25348999470613585085471)
                      ·
                        rfl

theorem cell23_49367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_49367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_49367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_49367 prefixEnd_49367 := by exact prefixLift 49367
  have htrace : WordTrace (prefixWord ++ tailWord_49367) baseStart_49367 baseEnd_49367 := by
    simpa [prefixWord, tailWord_49367, baseEnd_49367] using wordTrace_append hprefix tailTrace_49367
  have hstable : (prefixWord ++ tailWord_49367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49367).length < 2 ^ (prefixWord ++ tailWord_49367).sum := by decide
  have hdescent : baseEnd_49367 < baseStart_49367 := by decide
  rcases family_descends (prefixWord ++ tailWord_49367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49381 : List Nat := [1, 3, 1, 4, 2, 1, 2, 3, 1, 1, 4]
def baseStart_49381 : Nat := 118140960795 + 49381 * 2 ^ 59
def prefixEnd_49381 : Nat := 4983230072969 + 3 ^ 40 * 49381 * 2
def baseEnd_49381 : Nat := 25356188199776530310407

theorem tailTrace_49381 : CollatzResearch.WordTrace tailWord_49381 prefixEnd_49381 25356188199776530310407 := by
  unfold tailWord_49381
  simp only [CollatzResearch.WordTrace]
  refine ⟨1801073034108545448475997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1200715356072363632317331 1801073034108545448475997)
  ·
    refine ⟨675402387790704543178499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1801073034108545448475997 675402387790704543178499)
    ·
      refine ⟨1013103581686056814767749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 675402387790704543178499 1013103581686056814767749)
      ·
        refine ⟨189956921566135652768953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1013103581686056814767749 189956921566135652768953)
        ·
          refine ⟨142467691174601739576715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189956921566135652768953 142467691174601739576715)
          ·
            refine ⟨213701536761902609365073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142467691174601739576715 213701536761902609365073)
            ·
              refine ⟨160276152571426957023805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 213701536761902609365073 160276152571426957023805)
              ·
                refine ⟨60103557214285108883927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 160276152571426957023805 60103557214285108883927)
                ·
                  refine ⟨90155335821427663325891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60103557214285108883927 90155335821427663325891)
                  ·
                    refine ⟨135233003732141494988837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 90155335821427663325891 135233003732141494988837)
                    ·
                      refine ⟨25356188199776530310407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 135233003732141494988837 25356188199776530310407)
                      ·
                        rfl

theorem cell23_49381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_49381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_49381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_49381 prefixEnd_49381 := by exact prefixLift 49381
  have htrace : WordTrace (prefixWord ++ tailWord_49381) baseStart_49381 baseEnd_49381 := by
    simpa [prefixWord, tailWord_49381, baseEnd_49381] using wordTrace_append hprefix tailTrace_49381
  have hstable : (prefixWord ++ tailWord_49381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49381).length < 2 ^ (prefixWord ++ tailWord_49381).sum := by decide
  have hdescent : baseEnd_49381 < baseStart_49381 := by decide
  rcases family_descends (prefixWord ++ tailWord_49381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49384 : List Nat := [2, 1, 4, 1, 2, 2, 1, 3, 1, 1, 5]
def baseStart_49384 : Nat := 118140960795 + 49384 * 2 ^ 59
def prefixEnd_49384 : Nat := 4983230072969 + 3 ^ 40 * 49384 * 2
def baseEnd_49384 : Nat := 25357728641740018572893

theorem tailTrace_49384 : CollatzResearch.WordTrace tailWord_49384 prefixEnd_49384 25357728641740018572893 := by
  unfold tailWord_49384
  simp only [CollatzResearch.WordTrace]
  refine ⟨900591226548838480417603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1200788302065117973890137 900591226548838480417603)
  ·
    refine ⟨1350886839823257720626405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 900591226548838480417603 1350886839823257720626405)
    ·
      refine ⟨253291282466860822617451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1350886839823257720626405 253291282466860822617451)
      ·
        refine ⟨379936923700291233926177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253291282466860822617451 379936923700291233926177)
        ·
          refine ⟨284952692775218425444633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 379936923700291233926177 284952692775218425444633)
          ·
            refine ⟨213714519581413819083475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 284952692775218425444633 213714519581413819083475)
            ·
              refine ⟨320571779372120728625213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213714519581413819083475 320571779372120728625213)
              ·
                refine ⟨120214417264545273234455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 320571779372120728625213 120214417264545273234455)
                ·
                  refine ⟨180321625896817909851683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120214417264545273234455 180321625896817909851683)
                  ·
                    refine ⟨270482438845226864777525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 180321625896817909851683 270482438845226864777525)
                    ·
                      refine ⟨25357728641740018572893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 270482438845226864777525 25357728641740018572893)
                      ·
                        rfl

theorem cell23_49384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_49384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_49384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_49384 prefixEnd_49384 := by exact prefixLift 49384
  have htrace : WordTrace (prefixWord ++ tailWord_49384) baseStart_49384 baseEnd_49384 := by
    simpa [prefixWord, tailWord_49384, baseEnd_49384] using wordTrace_append hprefix tailTrace_49384
  have hstable : (prefixWord ++ tailWord_49384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49384).length < 2 ^ (prefixWord ++ tailWord_49384).sum := by decide
  have hdescent : baseEnd_49384 < baseStart_49384 := by decide
  rcases family_descends (prefixWord ++ tailWord_49384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49394 : List Nat := [3, 2, 1, 3, 2, 1, 1, 2, 1, 1, 6]
def baseStart_49394 : Nat := 118140960795 + 49394 * 2 ^ 59
def prefixEnd_49394 : Nat := 4983230072969 + 3 ^ 40 * 49394 * 2
def baseEnd_49394 : Nat := 25362863448284979447847

theorem tailTrace_49394 : CollatzResearch.WordTrace tailWord_49394 prefixEnd_49394 25362863448284979447847 := by
  unfold tailWord_49394
  simp only [CollatzResearch.WordTrace]
  refine ⟨450386795765362167174809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1201031455374299112466157 450386795765362167174809)
  ·
    refine ⟨337790096824021625381107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 450386795765362167174809 337790096824021625381107)
    ·
      refine ⟨506685145236032438071661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337790096824021625381107 506685145236032438071661)
      ·
        refine ⟨190006929463512164276873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 506685145236032438071661 190006929463512164276873)
        ·
          refine ⟨142505197097634123207655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190006929463512164276873 142505197097634123207655)
          ·
            refine ⟨213757795646451184811483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142505197097634123207655 213757795646451184811483)
            ·
              refine ⟨320636693469676777217225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213757795646451184811483 320636693469676777217225)
              ·
                refine ⟨240477520102257582912919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 320636693469676777217225 240477520102257582912919)
                ·
                  refine ⟨360716280153386374369379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 240477520102257582912919 360716280153386374369379)
                  ·
                    refine ⟨541074420230079561554069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 360716280153386374369379 541074420230079561554069)
                    ·
                      refine ⟨25362863448284979447847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 541074420230079561554069 25362863448284979447847)
                      ·
                        rfl

theorem cell23_49394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_49394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_49394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_49394 prefixEnd_49394 := by exact prefixLift 49394
  have htrace : WordTrace (prefixWord ++ tailWord_49394) baseStart_49394 baseEnd_49394 := by
    simpa [prefixWord, tailWord_49394, baseEnd_49394] using wordTrace_append hprefix tailTrace_49394
  have hstable : (prefixWord ++ tailWord_49394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49394).length < 2 ^ (prefixWord ++ tailWord_49394).sum := by decide
  have hdescent : baseEnd_49394 < baseStart_49394 := by decide
  rcases family_descends (prefixWord ++ tailWord_49394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49404 : List Nat := [2, 2, 2, 1, 4, 2, 2, 8]
def baseStart_49404 : Nat := 118140960795 + 49404 * 2 ^ 59
def prefixEnd_49404 : Nat := 4983230072969 + 3 ^ 40 * 49404 * 2
def baseEnd_49404 : Nat := 939555490919627419363

theorem tailTrace_49404 : CollatzResearch.WordTrace tailWord_49404 prefixEnd_49404 939555490919627419363 := by
  unfold tailWord_49404
  simp only [CollatzResearch.WordTrace]
  refine ⟨900955956512610188281633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1201274608683480251042177 900955956512610188281633)
  ·
    refine ⟨675716967384457641211225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 900955956512610188281633 675716967384457641211225)
    ·
      refine ⟨506787725538343230908419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 675716967384457641211225 506787725538343230908419)
      ·
        refine ⟨760181588307514846362629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 506787725538343230908419 760181588307514846362629)
        ·
          refine ⟨142534047807659033692993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 760181588307514846362629 142534047807659033692993)
          ·
            refine ⟨106900535855744275269745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142534047807659033692993 106900535855744275269745)
            ·
              refine ⟨80175401891808206452309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106900535855744275269745 80175401891808206452309)
              ·
                refine ⟨939555490919627419363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 80175401891808206452309 939555490919627419363)
                ·
                  rfl

theorem cell23_49404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 8].length) (baseStart_49404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_49404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_49404 prefixEnd_49404 := by exact prefixLift 49404
  have htrace : WordTrace (prefixWord ++ tailWord_49404) baseStart_49404 baseEnd_49404 := by
    simpa [prefixWord, tailWord_49404, baseEnd_49404] using wordTrace_append hprefix tailTrace_49404
  have hstable : (prefixWord ++ tailWord_49404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49404).length < 2 ^ (prefixWord ++ tailWord_49404).sum := by decide
  have hdescent : baseEnd_49404 < baseStart_49404 := by decide
  rcases family_descends (prefixWord ++ tailWord_49404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49407 : List Nat := [1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 6]
def baseStart_49407 : Nat := 118140960795 + 49407 * 2 ^ 59
def prefixEnd_49407 : Nat := 4983230072969 + 3 ^ 40 * 49407 * 2
def baseEnd_49407 : Nat := 25369538696793428585287

theorem tailTrace_49407 : CollatzResearch.WordTrace tailWord_49407 prefixEnd_49407 25369538696793428585287 := by
  unfold tailWord_49407
  simp only [CollatzResearch.WordTrace]
  refine ⟨1802021332014351888922475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1201347554676234592614983 1802021332014351888922475)
  ·
    refine ⟨2703031998021527833383713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1802021332014351888922475 2703031998021527833383713)
    ·
      refine ⟨2027273998516145875037785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2703031998021527833383713 2027273998516145875037785)
      ·
        refine ⟨1520455498887109406278339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2027273998516145875037785 1520455498887109406278339)
        ·
          refine ⟨2280683248330664109417509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1520455498887109406278339 2280683248330664109417509)
          ·
            refine ⟨427628109061999520515783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2280683248330664109417509 427628109061999520515783)
            ·
              refine ⟨641442163592999280773675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 427628109061999520515783 641442163592999280773675)
              ·
                refine ⟨962163245389498921160513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 641442163592999280773675 962163245389498921160513)
                ·
                  refine ⟨721622434042124190870385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 962163245389498921160513 721622434042124190870385)
                  ·
                    refine ⟨541216825531593143152789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 721622434042124190870385 541216825531593143152789)
                    ·
                      refine ⟨25369538696793428585287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 541216825531593143152789 25369538696793428585287)
                      ·
                        rfl

theorem cell23_49407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 6].length) (baseStart_49407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_49407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_49407 prefixEnd_49407 := by exact prefixLift 49407
  have htrace : WordTrace (prefixWord ++ tailWord_49407) baseStart_49407 baseEnd_49407 := by
    simpa [prefixWord, tailWord_49407, baseEnd_49407] using wordTrace_append hprefix tailTrace_49407
  have hstable : (prefixWord ++ tailWord_49407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49407).length < 2 ^ (prefixWord ++ tailWord_49407).sum := by decide
  have hdescent : baseEnd_49407 < baseStart_49407 := by decide
  rcases family_descends (prefixWord ++ tailWord_49407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49415 : List Nat := [1, 1, 4, 5, 1, 2, 1, 2, 1, 1, 4]
def baseStart_49415 : Nat := 118140960795 + 49415 * 2 ^ 59
def prefixEnd_49415 : Nat := 4983230072969 + 3 ^ 40 * 49415 * 2
def baseEnd_49415 : Nat := 25373646542029397285251

theorem tailTrace_49415 : CollatzResearch.WordTrace tailWord_49415 prefixEnd_49415 25373646542029397285251 := by
  unfold tailWord_49415
  simp only [CollatzResearch.WordTrace]
  refine ⟨1802313115985369255213699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1201542077323579503475799 1802313115985369255213699)
  ·
    refine ⟨2703469673978053882820549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1802313115985369255213699 2703469673978053882820549)
    ·
      refine ⟨506900563870885103028853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2703469673978053882820549 506900563870885103028853)
      ·
        refine ⟨47521927862895478408955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 506900563870885103028853 47521927862895478408955)
        ·
          refine ⟨71282891794343217613433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47521927862895478408955 71282891794343217613433)
          ·
            refine ⟨53462168845757413210075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71282891794343217613433 53462168845757413210075)
            ·
              refine ⟨80193253268636119815113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53462168845757413210075 80193253268636119815113)
              ·
                refine ⟨60144939951477089861335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80193253268636119815113 60144939951477089861335)
                ·
                  refine ⟨90217409927215634792003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60144939951477089861335 90217409927215634792003)
                  ·
                    refine ⟨135326114890823452188005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 90217409927215634792003 135326114890823452188005)
                    ·
                      refine ⟨25373646542029397285251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 135326114890823452188005 25373646542029397285251)
                      ·
                        rfl

theorem cell23_49415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_49415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_49415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_49415 prefixEnd_49415 := by exact prefixLift 49415
  have htrace : WordTrace (prefixWord ++ tailWord_49415) baseStart_49415 baseEnd_49415 := by
    simpa [prefixWord, tailWord_49415, baseEnd_49415] using wordTrace_append hprefix tailTrace_49415
  have hstable : (prefixWord ++ tailWord_49415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49415).length < 2 ^ (prefixWord ++ tailWord_49415).sum := by decide
  have hdescent : baseEnd_49415 < baseStart_49415 := by decide
  rcases family_descends (prefixWord ++ tailWord_49415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49427 : List Nat := [1, 1, 1, 2, 1, 3, 1, 3, 1, 4, 5]
def baseStart_49427 : Nat := 118140960795 + 49427 * 2 ^ 59
def prefixEnd_49427 : Nat := 4983230072969 + 3 ^ 40 * 49427 * 2
def baseEnd_49427 : Nat := 25379808309883350335195

theorem tailTrace_49427 : CollatzResearch.WordTrace tailWord_49427 prefixEnd_49427 25379808309883350335195 := by
  unfold tailWord_49427
  simp only [CollatzResearch.WordTrace]
  refine ⟨1802750791941895304650535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1201833861294596869767023 1802750791941895304650535)
  ·
    refine ⟨2704126187912842956975803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1802750791941895304650535 2704126187912842956975803)
    ·
      refine ⟨4056189281869264435463705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2704126187912842956975803 4056189281869264435463705)
      ·
        refine ⟨3042141961401948326597779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4056189281869264435463705 3042141961401948326597779)
        ·
          refine ⟨4563212942102922489896669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3042141961401948326597779 4563212942102922489896669)
          ·
            refine ⟨1711204853288595933711251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4563212942102922489896669 1711204853288595933711251)
            ·
              refine ⟨2566807279932893900566877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1711204853288595933711251 2566807279932893900566877)
              ·
                refine ⟨962552729974835212712579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2566807279932893900566877 962552729974835212712579)
                ·
                  refine ⟨1443829094962252819068869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 962552729974835212712579 1443829094962252819068869)
                  ·
                    refine ⟨270717955305422403575413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1443829094962252819068869 270717955305422403575413)
                    ·
                      refine ⟨25379808309883350335195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 270717955305422403575413 25379808309883350335195)
                      ·
                        rfl

theorem cell23_49427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 4, 5].length) (baseStart_49427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_49427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_49427 prefixEnd_49427 := by exact prefixLift 49427
  have htrace : WordTrace (prefixWord ++ tailWord_49427) baseStart_49427 baseEnd_49427 := by
    simpa [prefixWord, tailWord_49427, baseEnd_49427] using wordTrace_append hprefix tailTrace_49427
  have hstable : (prefixWord ++ tailWord_49427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49427).length < 2 ^ (prefixWord ++ tailWord_49427).sum := by decide
  have hdescent : baseEnd_49427 < baseStart_49427 := by decide
  rcases family_descends (prefixWord ++ tailWord_49427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49431 : List Nat := [1, 1, 3, 4, 1, 3, 1, 2, 1, 3, 3]
def baseStart_49431 : Nat := 118140960795 + 49431 * 2 ^ 59
def prefixEnd_49431 : Nat := 4983230072969 + 3 ^ 40 * 49431 * 2
def baseEnd_49431 : Nat := 25381862232501334685177

theorem tailTrace_49431 : CollatzResearch.WordTrace tailWord_49431 prefixEnd_49431 25381862232501334685177 := by
  unfold tailWord_49431
  simp only [CollatzResearch.WordTrace]
  refine ⟨1802896683927403987796147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1201931122618269325197431 1802896683927403987796147)
  ·
    refine ⟨2704345025891105981694221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1802896683927403987796147 2704345025891105981694221)
    ·
      refine ⟨1014129384709164743135333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2704345025891105981694221 1014129384709164743135333)
      ·
        refine ⟨190149259632968389337875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1014129384709164743135333 190149259632968389337875)
        ·
          refine ⟨285223889449452584006813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190149259632968389337875 285223889449452584006813)
          ·
            refine ⟨106958958543544719002555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 285223889449452584006813 106958958543544719002555)
            ·
              refine ⟨160438437815317078503833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106958958543544719002555 160438437815317078503833)
              ·
                refine ⟨120328828361487808877875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160438437815317078503833 120328828361487808877875)
                ·
                  refine ⟨180493242542231713316813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120328828361487808877875 180493242542231713316813)
                  ·
                    refine ⟨67684965953336892493805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 180493242542231713316813 67684965953336892493805)
                    ·
                      refine ⟨25381862232501334685177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 67684965953336892493805 25381862232501334685177)
                      ·
                        rfl

theorem cell23_49431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_49431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_49431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_49431 prefixEnd_49431 := by exact prefixLift 49431
  have htrace : WordTrace (prefixWord ++ tailWord_49431) baseStart_49431 baseEnd_49431 := by
    simpa [prefixWord, tailWord_49431, baseEnd_49431] using wordTrace_append hprefix tailTrace_49431
  have hstable : (prefixWord ++ tailWord_49431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49431).length < 2 ^ (prefixWord ++ tailWord_49431).sum := by decide
  have hdescent : baseEnd_49431 < baseStart_49431 := by decide
  rcases family_descends (prefixWord ++ tailWord_49431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49484 : List Nat := [2, 2, 1, 3, 2, 1, 1, 2, 1, 4, 4]
def baseStart_49484 : Nat := 118140960795 + 49484 * 2 ^ 59
def prefixEnd_49484 : Nat := 4983230072969 + 3 ^ 40 * 49484 * 2
def baseEnd_49484 : Nat := 25409076707189627322433

theorem tailTrace_49484 : CollatzResearch.WordTrace tailWord_49484 prefixEnd_49484 25409076707189627322433 := by
  unfold tailWord_49484
  simp only [CollatzResearch.WordTrace]
  refine ⟨902414876367697019737753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1203219835156929359650337 902414876367697019737753)
  ·
    refine ⟨676811157275772764803315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 902414876367697019737753 676811157275772764803315)
    ·
      refine ⟨1015216735913659147204973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 676811157275772764803315 1015216735913659147204973)
      ·
        refine ⟨380706275967622180201865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1015216735913659147204973 380706275967622180201865)
        ·
          refine ⟨285529706975716635151399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 380706275967622180201865 285529706975716635151399)
          ·
            refine ⟨428294560463574952727099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285529706975716635151399 428294560463574952727099)
            ·
              refine ⟨642441840695362429090649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 428294560463574952727099 642441840695362429090649)
              ·
                refine ⟨481831380521521821817987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 642441840695362429090649 481831380521521821817987)
                ·
                  refine ⟨722747070782282732726981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 481831380521521821817987 722747070782282732726981)
                  ·
                    refine ⟨135515075771678012386309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 722747070782282732726981 135515075771678012386309)
                    ·
                      refine ⟨25409076707189627322433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 135515075771678012386309 25409076707189627322433)
                      ·
                        rfl

theorem cell23_49484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_49484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_49484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_49484 prefixEnd_49484 := by exact prefixLift 49484
  have htrace : WordTrace (prefixWord ++ tailWord_49484) baseStart_49484 baseEnd_49484 := by
    simpa [prefixWord, tailWord_49484, baseEnd_49484] using wordTrace_append hprefix tailTrace_49484
  have hstable : (prefixWord ++ tailWord_49484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49484).length < 2 ^ (prefixWord ++ tailWord_49484).sum := by decide
  have hdescent : baseEnd_49484 < baseStart_49484 := by decide
  rcases family_descends (prefixWord ++ tailWord_49484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49492 : List Nat := [2, 4, 1, 1, 2, 4, 2, 1, 1, 3, 2]
def baseStart_49492 : Nat := 118140960795 + 49492 * 2 ^ 59
def prefixEnd_49492 : Nat := 4983230072969 + 3 ^ 40 * 49492 * 2
def baseEnd_49492 : Nat := 25413184552425596022397

theorem tailTrace_49492 : CollatzResearch.WordTrace tailWord_49492 prefixEnd_49492 25413184552425596022397 := by
  unfold tailWord_49492
  simp only [CollatzResearch.WordTrace]
  refine ⟨902560768353205702883365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1203414357804274270511153 902560768353205702883365)
  ·
    refine ⟨169230144066226069290631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 902560768353205702883365 169230144066226069290631)
    ·
      refine ⟨253845216099339103935947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169230144066226069290631 253845216099339103935947)
      ·
        refine ⟨380767824149008655903921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253845216099339103935947 380767824149008655903921)
        ·
          refine ⟨285575868111756491927941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 380767824149008655903921 285575868111756491927941)
          ·
            refine ⟨53545475270954342236489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 285575868111756491927941 53545475270954342236489)
            ·
              refine ⟨40159106453215756677367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53545475270954342236489 40159106453215756677367)
              ·
                refine ⟨60238659679823635016051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40159106453215756677367 60238659679823635016051)
                ·
                  refine ⟨90357989519735452524077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60238659679823635016051 90357989519735452524077)
                  ·
                    refine ⟨33884246069900794696529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 90357989519735452524077 33884246069900794696529)
                    ·
                      refine ⟨25413184552425596022397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 33884246069900794696529 25413184552425596022397)
                      ·
                        rfl

theorem cell23_49492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 2, 1, 1, 3, 2].length) (baseStart_49492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_49492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_49492 prefixEnd_49492 := by exact prefixLift 49492
  have htrace : WordTrace (prefixWord ++ tailWord_49492) baseStart_49492 baseEnd_49492 := by
    simpa [prefixWord, tailWord_49492, baseEnd_49492] using wordTrace_append hprefix tailTrace_49492
  have hstable : (prefixWord ++ tailWord_49492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49492).length < 2 ^ (prefixWord ++ tailWord_49492).sum := by decide
  have hdescent : baseEnd_49492 < baseStart_49492 := by decide
  rcases family_descends (prefixWord ++ tailWord_49492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49511 : List Nat := [1, 1, 5, 1, 3, 2, 2, 1, 7]
def baseStart_49511 : Nat := 118140960795 + 49511 * 2 ^ 59
def prefixEnd_49511 : Nat := 4983230072969 + 3 ^ 40 * 49511 * 2
def baseEnd_49511 : Nat := 2824771187206780187201

theorem tailTrace_49511 : CollatzResearch.WordTrace tailWord_49511 prefixEnd_49511 2824771187206780187201 := by
  unfold tailWord_49511
  simp only [CollatzResearch.WordTrace]
  refine ⟨1805814523637577650708387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1203876349091718433805591 1805814523637577650708387)
  ·
    refine ⟨2708721785456366476062581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1805814523637577650708387 2708721785456366476062581)
    ·
      refine ⟨253942667386534357130867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2708721785456366476062581 253942667386534357130867)
      ·
        refine ⟨380914001079801535696301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253942667386534357130867 380914001079801535696301)
        ·
          refine ⟨142842750404925575886113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 380914001079801535696301 142842750404925575886113)
          ·
            refine ⟨107132062803694181914585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142842750404925575886113 107132062803694181914585)
            ·
              refine ⟨80349047102770636435939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107132062803694181914585 80349047102770636435939)
              ·
                refine ⟨120523570654155954653909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80349047102770636435939 120523570654155954653909)
                ·
                  refine ⟨2824771187206780187201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 120523570654155954653909 2824771187206780187201)
                  ·
                    rfl

theorem cell23_49511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 1, 7].length) (baseStart_49511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_49511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_49511 prefixEnd_49511 := by exact prefixLift 49511
  have htrace : WordTrace (prefixWord ++ tailWord_49511) baseStart_49511 baseEnd_49511 := by
    simpa [prefixWord, tailWord_49511, baseEnd_49511] using wordTrace_append hprefix tailTrace_49511
  have hstable : (prefixWord ++ tailWord_49511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49511).length < 2 ^ (prefixWord ++ tailWord_49511).sum := by decide
  have hdescent : baseEnd_49511 < baseStart_49511 := by decide
  rcases family_descends (prefixWord ++ tailWord_49511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49522 : List Nat := [3, 2, 1, 2, 1, 4, 3, 1, 2, 2, 2]
def baseStart_49522 : Nat := 118140960795 + 49522 * 2 ^ 59
def prefixEnd_49522 : Nat := 4983230072969 + 3 ^ 40 * 49522 * 2
def baseEnd_49522 : Nat := 25428588972060478647259

theorem tailTrace_49522 : CollatzResearch.WordTrace tailWord_49522 prefixEnd_49522 25428588972060478647259 := by
  unfold tailWord_49522
  simp only [CollatzResearch.WordTrace]
  refine ⟨451553931649431632339705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1204143817731817686239213 451553931649431632339705)
  ·
    refine ⟨338665448737073724254779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 451553931649431632339705 338665448737073724254779)
    ·
      refine ⟨507998173105610586382169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338665448737073724254779 507998173105610586382169)
      ·
        refine ⟨380998629829207939786627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 507998173105610586382169 380998629829207939786627)
        ·
          refine ⟨571497944743811909679941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 380998629829207939786627 571497944743811909679941)
          ·
            refine ⟨107155864639464733064989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 571497944743811909679941 107155864639464733064989)
            ·
              refine ⟨40183449239799274899371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107155864639464733064989 40183449239799274899371)
              ·
                refine ⟨60275173859698912349057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40183449239799274899371 60275173859698912349057)
                ·
                  refine ⟨45206380394774184261793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60275173859698912349057 45206380394774184261793)
                  ·
                    refine ⟨33904785296080638196345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45206380394774184261793 33904785296080638196345)
                    ·
                      refine ⟨25428588972060478647259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 33904785296080638196345 25428588972060478647259)
                      ·
                        rfl

theorem cell23_49522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 3, 1, 2, 2, 2].length) (baseStart_49522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_49522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_49522 prefixEnd_49522 := by exact prefixLift 49522
  have htrace : WordTrace (prefixWord ++ tailWord_49522) baseStart_49522 baseEnd_49522 := by
    simpa [prefixWord, tailWord_49522, baseEnd_49522] using wordTrace_append hprefix tailTrace_49522
  have hstable : (prefixWord ++ tailWord_49522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49522).length < 2 ^ (prefixWord ++ tailWord_49522).sum := by decide
  have hdescent : baseEnd_49522 < baseStart_49522 := by decide
  rcases family_descends (prefixWord ++ tailWord_49522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49561 : List Nat := [1, 2, 1, 2, 1, 4, 3, 2, 2, 1, 4]
def baseStart_49561 : Nat := 118140960795 + 49561 * 2 ^ 59
def prefixEnd_49561 : Nat := 4983230072969 + 3 ^ 40 * 49561 * 2
def baseEnd_49561 : Nat := 25448614717585826059579

theorem tailTrace_49561 : CollatzResearch.WordTrace tailWord_49561 prefixEnd_49561 25448614717585826059579 := by
  unfold tailWord_49561
  simp only [CollatzResearch.WordTrace]
  refine ⟨1807638173456436190028537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1205092115637624126685691 1807638173456436190028537)
  ·
    refine ⟨1355728630092327142521403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1807638173456436190028537 1355728630092327142521403)
    ·
      refine ⟨2033592945138490713782105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1355728630092327142521403 2033592945138490713782105)
      ·
        refine ⟨1525194708853868035336579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2033592945138490713782105 1525194708853868035336579)
        ·
          refine ⟨2287792063280802053004869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1525194708853868035336579 2287792063280802053004869)
          ·
            refine ⟨428961011865150384938413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2287792063280802053004869 428961011865150384938413)
            ·
              refine ⟨160860379449431394351905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 428961011865150384938413 160860379449431394351905)
              ·
                refine ⟨120645284587073545763929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160860379449431394351905 120645284587073545763929)
                ·
                  refine ⟨90483963440305159322947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120645284587073545763929 90483963440305159322947)
                  ·
                    refine ⟨135725945160457738984421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 90483963440305159322947 135725945160457738984421)
                    ·
                      refine ⟨25448614717585826059579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 135725945160457738984421 25448614717585826059579)
                      ·
                        rfl

theorem cell23_49561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 2, 2, 1, 4].length) (baseStart_49561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_49561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_49561 prefixEnd_49561 := by exact prefixLift 49561
  have htrace : WordTrace (prefixWord ++ tailWord_49561) baseStart_49561 baseEnd_49561 := by
    simpa [prefixWord, tailWord_49561, baseEnd_49561] using wordTrace_append hprefix tailTrace_49561
  have hstable : (prefixWord ++ tailWord_49561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49561).length < 2 ^ (prefixWord ++ tailWord_49561).sum := by decide
  have hdescent : baseEnd_49561 < baseStart_49561 := by decide
  rcases family_descends (prefixWord ++ tailWord_49561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49598 : List Nat := [4, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3]
def baseStart_49598 : Nat := 118140960795 + 49598 * 2 ^ 59
def prefixEnd_49598 : Nat := 4983230072969 + 3 ^ 40 * 49598 * 2
def baseEnd_49598 : Nat := 25467613501802181296909

theorem tailTrace_49598 : CollatzResearch.WordTrace tailWord_49598 prefixEnd_49598 25467613501802181296909 := by
  unfold tailWord_49598
  simp only [CollatzResearch.WordTrace]
  refine ⟨226123459290298938640681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1205991782881594339416965 226123459290298938640681)
  ·
    refine ⟨169592594467724203980511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226123459290298938640681 169592594467724203980511)
    ·
      refine ⟨254388891701586305970767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169592594467724203980511 254388891701586305970767)
      ·
        refine ⟨381583337552379458956151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254388891701586305970767 381583337552379458956151)
        ·
          refine ⟨572375006328569188434227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381583337552379458956151 572375006328569188434227)
          ·
            refine ⟨858562509492853782651341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 572375006328569188434227 858562509492853782651341)
            ·
              refine ⟨321960941059820168494253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 858562509492853782651341 321960941059820168494253)
              ·
                refine ⟨120735352897432563185345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 321960941059820168494253 120735352897432563185345)
                ·
                  refine ⟨90551514673074422389009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120735352897432563185345 90551514673074422389009)
                  ·
                    refine ⟨67913636004805816791757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 90551514673074422389009 67913636004805816791757)
                    ·
                      refine ⟨25467613501802181296909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 67913636004805816791757 25467613501802181296909)
                      ·
                        rfl

theorem cell23_49598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_49598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_49598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_49598 prefixEnd_49598 := by exact prefixLift 49598
  have htrace : WordTrace (prefixWord ++ tailWord_49598) baseStart_49598 baseEnd_49598 := by
    simpa [prefixWord, tailWord_49598, baseEnd_49598] using wordTrace_append hprefix tailTrace_49598
  have hstable : (prefixWord ++ tailWord_49598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49598).length < 2 ^ (prefixWord ++ tailWord_49598).sum := by decide
  have hdescent : baseEnd_49598 < baseStart_49598 := by decide
  rcases family_descends (prefixWord ++ tailWord_49598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49622 : List Nat := [5, 2, 1, 1, 1, 1, 3, 4, 1, 4]
def baseStart_49622 : Nat := 118140960795 + 49622 * 2 ^ 59
def prefixEnd_49622 : Nat := 4983230072969 + 3 ^ 40 * 49622 * 2
def baseEnd_49622 : Nat := 8493312345836695798933

theorem tailTrace_49622 : CollatzResearch.WordTrace tailWord_49622 prefixEnd_49622 8493312345836695798933 := by
  unfold tailWord_49622
  simp only [CollatzResearch.WordTrace]
  refine ⟨113116439139715225499945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1206575350823629071999413 113116439139715225499945)
  ·
    refine ⟨84837329354786419124959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113116439139715225499945 84837329354786419124959)
    ·
      refine ⟨127255994032179628687439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84837329354786419124959 127255994032179628687439)
      ·
        refine ⟨190883991048269443031159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127255994032179628687439 190883991048269443031159)
        ·
          refine ⟨286325986572404164546739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190883991048269443031159 286325986572404164546739)
          ·
            refine ⟨429488979858606246820109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286325986572404164546739 429488979858606246820109)
            ·
              refine ⟨161058367446977342557541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 429488979858606246820109 161058367446977342557541)
              ·
                refine ⟨30198443896308251729539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 161058367446977342557541 30198443896308251729539)
                ·
                  refine ⟨45297665844462377594309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30198443896308251729539 45297665844462377594309)
                  ·
                    refine ⟨8493312345836695798933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45297665844462377594309 8493312345836695798933)
                    ·
                      rfl

theorem cell23_49622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_49622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_49622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_49622 prefixEnd_49622 := by exact prefixLift 49622
  have htrace : WordTrace (prefixWord ++ tailWord_49622) baseStart_49622 baseEnd_49622 := by
    simpa [prefixWord, tailWord_49622, baseEnd_49622] using wordTrace_append hprefix tailTrace_49622
  have hstable : (prefixWord ++ tailWord_49622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49622).length < 2 ^ (prefixWord ++ tailWord_49622).sum := by decide
  have hdescent : baseEnd_49622 < baseStart_49622 := by decide
  rcases family_descends (prefixWord ++ tailWord_49622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49631 : List Nat := [1, 1, 2, 3, 3, 2, 1, 2, 3, 5]
def baseStart_49631 : Nat := 118140960795 + 49631 * 2 ^ 59
def prefixEnd_49631 : Nat := 4983230072969 + 3 ^ 40 * 49631 * 2
def baseEnd_49631 : Nat := 8494852787800184061419

theorem tailTrace_49631 : CollatzResearch.WordTrace tailWord_49631 prefixEnd_49631 8494852787800184061419 := by
  unfold tailWord_49631
  simp only [CollatzResearch.WordTrace]
  refine ⟨1810191283202838145076747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1206794188801892096717831 1810191283202838145076747)
  ·
    refine ⟨2715286924804257217615121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1810191283202838145076747 2715286924804257217615121)
    ·
      refine ⟨2036465193603192913211341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2715286924804257217615121 2036465193603192913211341)
      ·
        refine ⟨763674447601197342454253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2036465193603192913211341 763674447601197342454253)
        ·
          refine ⟨286377917850449003420345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 763674447601197342454253 286377917850449003420345)
          ·
            refine ⟨214783438387836752565259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 286377917850449003420345 214783438387836752565259)
            ·
              refine ⟨322175157581755128847889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214783438387836752565259 322175157581755128847889)
              ·
                refine ⟨241631368186316346635917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 322175157581755128847889 241631368186316346635917)
                ·
                  refine ⟨90611763069868629988469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 241631368186316346635917 90611763069868629988469)
                  ·
                    refine ⟨8494852787800184061419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 90611763069868629988469 8494852787800184061419)
                    ·
                      rfl

theorem cell23_49631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 3, 5].length) (baseStart_49631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_49631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_49631 prefixEnd_49631 := by exact prefixLift 49631
  have htrace : WordTrace (prefixWord ++ tailWord_49631) baseStart_49631 baseEnd_49631 := by
    simpa [prefixWord, tailWord_49631, baseEnd_49631] using wordTrace_append hprefix tailTrace_49631
  have hstable : (prefixWord ++ tailWord_49631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49631).length < 2 ^ (prefixWord ++ tailWord_49631).sum := by decide
  have hdescent : baseEnd_49631 < baseStart_49631 := by decide
  rcases family_descends (prefixWord ++ tailWord_49631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49645 : List Nat := [1, 5, 1, 3, 1, 1, 1, 1, 5, 1, 3]
def baseStart_49645 : Nat := 118140960795 + 49645 * 2 ^ 59
def prefixEnd_49645 : Nat := 4983230072969 + 3 ^ 40 * 49645 * 2
def baseEnd_49645 : Nat := 25491747092563497409193

theorem tailTrace_49645 : CollatzResearch.WordTrace tailWord_49645 prefixEnd_49645 25491747092563497409193 := by
  unfold tailWord_49645
  simp only [CollatzResearch.WordTrace]
  refine ⟨1810701905152118536086389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1207134603434745690724259 1810701905152118536086389)
  ·
    refine ⟨169753303608011112758099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1810701905152118536086389 169753303608011112758099)
    ·
      refine ⟨254629955412016669137149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169753303608011112758099 254629955412016669137149)
      ·
        refine ⟨95486233279506250926431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 254629955412016669137149 95486233279506250926431)
        ·
          refine ⟨143229349919259376389647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95486233279506250926431 143229349919259376389647)
          ·
            refine ⟨214844024878889064584471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143229349919259376389647 214844024878889064584471)
            ·
              refine ⟨322266037318333596876707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214844024878889064584471 322266037318333596876707)
              ·
                refine ⟨483399055977500395315061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 322266037318333596876707 483399055977500395315061)
                ·
                  refine ⟨45318661497890662060787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 483399055977500395315061 45318661497890662060787)
                  ·
                    refine ⟨67977992246835993091181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45318661497890662060787 67977992246835993091181)
                    ·
                      refine ⟨25491747092563497409193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 67977992246835993091181 25491747092563497409193)
                      ·
                        rfl

theorem cell23_49645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_49645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_49645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_49645 prefixEnd_49645 := by exact prefixLift 49645
  have htrace : WordTrace (prefixWord ++ tailWord_49645) baseStart_49645 baseEnd_49645 := by
    simpa [prefixWord, tailWord_49645, baseEnd_49645] using wordTrace_append hprefix tailTrace_49645
  have hstable : (prefixWord ++ tailWord_49645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49645).length < 2 ^ (prefixWord ++ tailWord_49645).sum := by decide
  have hdescent : baseEnd_49645 < baseStart_49645 := by decide
  rcases family_descends (prefixWord ++ tailWord_49645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49651 : List Nat := [1, 1, 1, 2, 2, 2, 3, 3, 3, 1, 4]
def baseStart_49651 : Nat := 118140960795 + 49651 * 2 ^ 59
def prefixEnd_49651 : Nat := 4983230072969 + 3 ^ 40 * 49651 * 2
def baseEnd_49651 : Nat := 25494827976490473934165

theorem tailTrace_49651 : CollatzResearch.WordTrace tailWord_49651 prefixEnd_49651 25494827976490473934165 := by
  unfold tailWord_49651
  simp only [CollatzResearch.WordTrace]
  refine ⟨1810920743130381560804807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1207280495420254373869871 1810920743130381560804807)
  ·
    refine ⟨2716381114695572341207211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1810920743130381560804807 2716381114695572341207211)
    ·
      refine ⟨4074571672043358511810817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2716381114695572341207211 4074571672043358511810817)
      ·
        refine ⟨3055928754032518883858113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4074571672043358511810817 3055928754032518883858113)
        ·
          refine ⟨2291946565524389162893585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3055928754032518883858113 2291946565524389162893585)
          ·
            refine ⟨1718959924143291872170189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2291946565524389162893585 1718959924143291872170189)
            ·
              refine ⟨644609971553734452063821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1718959924143291872170189 644609971553734452063821)
              ·
                refine ⟨241728739332650419523933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 644609971553734452063821 241728739332650419523933)
                ·
                  refine ⟨90648277249743907321475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 241728739332650419523933 90648277249743907321475)
                  ·
                    refine ⟨135972415874615860982213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 90648277249743907321475 135972415874615860982213)
                    ·
                      refine ⟨25494827976490473934165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 135972415874615860982213 25494827976490473934165)
                      ·
                        rfl

theorem cell23_49651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 1, 4].length) (baseStart_49651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_49651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_49651 prefixEnd_49651 := by exact prefixLift 49651
  have htrace : WordTrace (prefixWord ++ tailWord_49651) baseStart_49651 baseEnd_49651 := by
    simpa [prefixWord, tailWord_49651, baseEnd_49651] using wordTrace_append hprefix tailTrace_49651
  have hstable : (prefixWord ++ tailWord_49651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49651).length < 2 ^ (prefixWord ++ tailWord_49651).sum := by decide
  have hdescent : baseEnd_49651 < baseStart_49651 := by decide
  rcases family_descends (prefixWord ++ tailWord_49651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49661 : List Nat := [1, 4, 1, 1, 1, 3, 1, 4, 1, 6]
def baseStart_49661 : Nat := 118140960795 + 49661 * 2 ^ 59
def prefixEnd_49661 : Nat := 4983230072969 + 3 ^ 40 * 49661 * 2
def baseEnd_49661 : Nat := 8499987594345144936373

theorem tailTrace_49661 : CollatzResearch.WordTrace tailWord_49661 prefixEnd_49661 8499987594345144936373 := by
  unfold tailWord_49661
  simp only [CollatzResearch.WordTrace]
  refine ⟨1811285473094153268668837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1207523648729435512445891 1811285473094153268668837)
  ·
    refine ⟨339616026205153737875407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1811285473094153268668837 339616026205153737875407)
    ·
      refine ⟨509424039307730606813111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339616026205153737875407 509424039307730606813111)
      ·
        refine ⟨764136058961595910219667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 509424039307730606813111 764136058961595910219667)
        ·
          refine ⟨1146204088442393865329501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 764136058961595910219667 1146204088442393865329501)
          ·
            refine ⟨429826533165897699498563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1146204088442393865329501 429826533165897699498563)
            ·
              refine ⟨644739799748846549247845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 429826533165897699498563 644739799748846549247845)
              ·
                refine ⟨120888712452908727983971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 644739799748846549247845 120888712452908727983971)
                ·
                  refine ⟨181333068679363091975957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120888712452908727983971 181333068679363091975957)
                  ·
                    refine ⟨8499987594345144936373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 181333068679363091975957 8499987594345144936373)
                    ·
                      rfl

theorem cell23_49661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 4, 1, 6].length) (baseStart_49661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_49661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_49661 prefixEnd_49661 := by exact prefixLift 49661
  have htrace : WordTrace (prefixWord ++ tailWord_49661) baseStart_49661 baseEnd_49661 := by
    simpa [prefixWord, tailWord_49661, baseEnd_49661] using wordTrace_append hprefix tailTrace_49661
  have hstable : (prefixWord ++ tailWord_49661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49661).length < 2 ^ (prefixWord ++ tailWord_49661).sum := by decide
  have hdescent : baseEnd_49661 < baseStart_49661 := by decide
  rcases family_descends (prefixWord ++ tailWord_49661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49665 : List Nat := [1, 2, 4, 1, 3, 1, 4, 1, 1, 5]
def baseStart_49665 : Nat := 118140960795 + 49665 * 2 ^ 59
def prefixEnd_49665 : Nat := 4983230072969 + 3 ^ 40 * 49665 * 2
def baseEnd_49665 : Nat := 8500672235217806386367

theorem tailTrace_49665 : CollatzResearch.WordTrace tailWord_49665 prefixEnd_49665 8500672235217806386367 := by
  unfold tailWord_49665
  simp only [CollatzResearch.WordTrace]
  refine ⟨1811431365079661951814449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1207620910053107967876299 1811431365079661951814449)
  ·
    refine ⟨1358573523809746463860837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1811431365079661951814449 1358573523809746463860837)
    ·
      refine ⟨254732535714327461973907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1358573523809746463860837 254732535714327461973907)
      ·
        refine ⟨382098803571491192960861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254732535714327461973907 382098803571491192960861)
        ·
          refine ⟨143287051339309197360323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 382098803571491192960861 143287051339309197360323)
          ·
            refine ⟨214930577008963796040485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143287051339309197360323 214930577008963796040485)
            ·
              refine ⟨40299483189180711757591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 214930577008963796040485 40299483189180711757591)
              ·
                refine ⟨60449224783771067636387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40299483189180711757591 60449224783771067636387)
                ·
                  refine ⟨90673837175656601454581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60449224783771067636387 90673837175656601454581)
                  ·
                    refine ⟨8500672235217806386367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 90673837175656601454581 8500672235217806386367)
                    ·
                      rfl

theorem cell23_49665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 4, 1, 1, 5].length) (baseStart_49665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_49665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_49665 prefixEnd_49665 := by exact prefixLift 49665
  have htrace : WordTrace (prefixWord ++ tailWord_49665) baseStart_49665 baseEnd_49665 := by
    simpa [prefixWord, tailWord_49665, baseEnd_49665] using wordTrace_append hprefix tailTrace_49665
  have hstable : (prefixWord ++ tailWord_49665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49665).length < 2 ^ (prefixWord ++ tailWord_49665).sum := by decide
  have hdescent : baseEnd_49665 < baseStart_49665 := by decide
  rcases family_descends (prefixWord ++ tailWord_49665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49688 : List Nat := [2, 1, 2, 3, 3, 2, 1, 2, 1, 1, 5]
def baseStart_49688 : Nat := 118140960795 + 49688 * 2 ^ 59
def prefixEnd_49688 : Nat := 4983230072969 + 3 ^ 40 * 49688 * 2
def baseEnd_49688 : Nat := 25513826760706829171495

theorem tailTrace_49688 : CollatzResearch.WordTrace tailWord_49688 prefixEnd_49688 25513826760706829171495 := by
  unfold tailWord_49688
  simp only [CollatzResearch.WordTrace]
  refine ⟨906135121998168439950859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1208180162664224586601145 906135121998168439950859)
  ·
    refine ⟨1359202682997252659926289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 906135121998168439950859 1359202682997252659926289)
    ·
      refine ⟨1019402012247939494944717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1359202682997252659926289 1019402012247939494944717)
      ·
        refine ⟨382275754592977310604269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1019402012247939494944717 382275754592977310604269)
        ·
          refine ⟨143353407972366491476601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 382275754592977310604269 143353407972366491476601)
          ·
            refine ⟨107515055979274868607451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143353407972366491476601 107515055979274868607451)
            ·
              refine ⟨161272583968912302911177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107515055979274868607451 161272583968912302911177)
              ·
                refine ⟨120954437976684227183383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161272583968912302911177 120954437976684227183383)
                ·
                  refine ⟨181431656965026340775075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120954437976684227183383 181431656965026340775075)
                  ·
                    refine ⟨272147485447539511162613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 181431656965026340775075 272147485447539511162613)
                    ·
                      refine ⟨25513826760706829171495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 272147485447539511162613 25513826760706829171495)
                      ·
                        rfl

theorem cell23_49688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_49688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_49688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_49688 prefixEnd_49688 := by exact prefixLift 49688
  have htrace : WordTrace (prefixWord ++ tailWord_49688) baseStart_49688 baseEnd_49688 := by
    simpa [prefixWord, tailWord_49688, baseEnd_49688] using wordTrace_append hprefix tailTrace_49688
  have hstable : (prefixWord ++ tailWord_49688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49688).length < 2 ^ (prefixWord ++ tailWord_49688).sum := by decide
  have hdescent : baseEnd_49688 < baseStart_49688 := by decide
  rcases family_descends (prefixWord ++ tailWord_49688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49735 : List Nat := [1, 1, 4, 1, 4, 1, 2, 1, 4, 1, 3]
def baseStart_49735 : Nat := 118140960795 + 49735 * 2 ^ 59
def prefixEnd_49735 : Nat := 4983230072969 + 3 ^ 40 * 49735 * 2
def baseEnd_49735 : Nat := 25537960351468145283779

theorem tailTrace_49735 : CollatzResearch.WordTrace tailWord_49735 prefixEnd_49735 25537960351468145283779 := by
  unfold tailWord_49735
  simp only [CollatzResearch.WordTrace]
  refine ⟨1813984474826063906862659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1209322983217375937908439 1813984474826063906862659)
  ·
    refine ⟨2720976712239095860293989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1813984474826063906862659 2720976712239095860293989)
    ·
      refine ⟨510183133544830473805123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2720976712239095860293989 510183133544830473805123)
      ·
        refine ⟨765274700317245710707685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 510183133544830473805123 765274700317245710707685)
        ·
          refine ⟨143489006309483570757691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 765274700317245710707685 143489006309483570757691)
          ·
            refine ⟨215233509464225356136537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143489006309483570757691 215233509464225356136537)
            ·
              refine ⟨161425132098169017102403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 215233509464225356136537 161425132098169017102403)
              ·
                refine ⟨242137698147253525653605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161425132098169017102403 242137698147253525653605)
                ·
                  refine ⟨45400818402610036060051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 242137698147253525653605 45400818402610036060051)
                  ·
                    refine ⟨68101227603915054090077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45400818402610036060051 68101227603915054090077)
                    ·
                      refine ⟨25537960351468145283779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 68101227603915054090077 25537960351468145283779)
                      ·
                        rfl

theorem cell23_49735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 4, 1, 3].length) (baseStart_49735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_49735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_49735 prefixEnd_49735 := by exact prefixLift 49735
  have htrace : WordTrace (prefixWord ++ tailWord_49735) baseStart_49735 baseEnd_49735 := by
    simpa [prefixWord, tailWord_49735, baseEnd_49735] using wordTrace_append hprefix tailTrace_49735
  have hstable : (prefixWord ++ tailWord_49735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49735).length < 2 ^ (prefixWord ++ tailWord_49735).sum := by decide
  have hdescent : baseEnd_49735 < baseStart_49735 := by decide
  rcases family_descends (prefixWord ++ tailWord_49735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49751 : List Nat := [1, 1, 3, 2, 2, 2, 2, 1, 1, 8]
def baseStart_49751 : Nat := 118140960795 + 49751 * 2 ^ 59
def prefixEnd_49751 : Nat := 4983230072969 + 3 ^ 40 * 49751 * 2
def baseEnd_49751 : Nat := 8515392013980027561235

theorem tailTrace_49751 : CollatzResearch.WordTrace tailWord_49751 prefixEnd_49751 8515392013980027561235 := by
  unfold tailWord_49751
  simp only [CollatzResearch.WordTrace]
  refine ⟨1814568042768098639445107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1209712028512065759630071 1814568042768098639445107)
  ·
    refine ⟨2721852064152147959167661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1814568042768098639445107 2721852064152147959167661)
    ·
      refine ⟨1020694524057055484687873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2721852064152147959167661 1020694524057055484687873)
      ·
        refine ⟨765520893042791613515905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1020694524057055484687873 765520893042791613515905)
        ·
          refine ⟨574140669782093710136929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 765520893042791613515905 574140669782093710136929)
          ·
            refine ⟨430605502336570282602697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 574140669782093710136929 430605502336570282602697)
            ·
              refine ⟨322954126752427711952023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 430605502336570282602697 322954126752427711952023)
              ·
                refine ⟨484431190128641567928035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 322954126752427711952023 484431190128641567928035)
                ·
                  refine ⟨726646785192962351892053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 484431190128641567928035 726646785192962351892053)
                  ·
                    refine ⟨8515392013980027561235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 726646785192962351892053 8515392013980027561235)
                    ·
                      rfl

theorem cell23_49751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 8].length) (baseStart_49751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_49751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_49751 prefixEnd_49751 := by exact prefixLift 49751
  have htrace : WordTrace (prefixWord ++ tailWord_49751) baseStart_49751 baseEnd_49751 := by
    simpa [prefixWord, tailWord_49751, baseEnd_49751] using wordTrace_append hprefix tailTrace_49751
  have hstable : (prefixWord ++ tailWord_49751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49751).length < 2 ^ (prefixWord ++ tailWord_49751).sum := by decide
  have hdescent : baseEnd_49751 < baseStart_49751 := by decide
  rcases family_descends (prefixWord ++ tailWord_49751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49752 : List Nat := [2, 1, 2, 2, 1, 2, 6, 1, 2, 1, 3]
def baseStart_49752 : Nat := 118140960795 + 49752 * 2 ^ 59
def prefixEnd_49752 : Nat := 4983230072969 + 3 ^ 40 * 49752 * 2
def baseEnd_49752 : Nat := 25546689522594578771201

theorem tailTrace_49752 : CollatzResearch.WordTrace tailWord_49752 prefixEnd_49752 25546689522594578771201 := by
  unfold tailWord_49752
  simp only [CollatzResearch.WordTrace]
  refine ⟨907302257882237905115755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1209736343842983873487673 907302257882237905115755)
  ·
    refine ⟨1360953386823356857673633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 907302257882237905115755 1360953386823356857673633)
    ·
      refine ⟨1020715040117517643255225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1360953386823356857673633 1020715040117517643255225)
      ·
        refine ⟨765536280088138232441419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1020715040117517643255225 765536280088138232441419)
        ·
          refine ⟨1148304420132207348662129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 765536280088138232441419 1148304420132207348662129)
          ·
            refine ⟨861228315099155511496597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1148304420132207348662129 861228315099155511496597)
            ·
              refine ⟨40370077270272914601403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 861228315099155511496597 40370077270272914601403)
              ·
                refine ⟨60555115905409371902105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40370077270272914601403 60555115905409371902105)
                ·
                  refine ⟨45416336929057028926579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60555115905409371902105 45416336929057028926579)
                  ·
                    refine ⟨68124505393585543389869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45416336929057028926579 68124505393585543389869)
                    ·
                      refine ⟨25546689522594578771201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 68124505393585543389869 25546689522594578771201)
                      ·
                        rfl

theorem cell23_49752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6, 1, 2, 1, 3].length) (baseStart_49752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_49752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_49752 prefixEnd_49752 := by exact prefixLift 49752
  have htrace : WordTrace (prefixWord ++ tailWord_49752) baseStart_49752 baseEnd_49752 := by
    simpa [prefixWord, tailWord_49752, baseEnd_49752] using wordTrace_append hprefix tailTrace_49752
  have hstable : (prefixWord ++ tailWord_49752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49752).length < 2 ^ (prefixWord ++ tailWord_49752).sum := by decide
  have hdescent : baseEnd_49752 < baseStart_49752 := by decide
  rcases family_descends (prefixWord ++ tailWord_49752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49771 : List Nat := [1, 1, 1, 1, 2, 2, 1, 3, 3, 4, 4]
def baseStart_49771 : Nat := 118140960795 + 49771 * 2 ^ 59
def prefixEnd_49771 : Nat := 4983230072969 + 3 ^ 40 * 49771 * 2
def baseEnd_49771 : Nat := 25556445655030004433613

theorem tailTrace_49771 : CollatzResearch.WordTrace tailWord_49771 prefixEnd_49771 25556445655030004433613 := by
  unfold tailWord_49771
  simp only [CollatzResearch.WordTrace]
  refine ⟨1815297502695642055173167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1210198335130428036782111 1815297502695642055173167)
  ·
    refine ⟨2722946254043463082759751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1815297502695642055173167 2722946254043463082759751)
    ·
      refine ⟨4084419381065194624139627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2722946254043463082759751 4084419381065194624139627)
      ·
        refine ⟨6126629071597791936209441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4084419381065194624139627 6126629071597791936209441)
        ·
          refine ⟨4594971803698343952157081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6126629071597791936209441 4594971803698343952157081)
          ·
            refine ⟨3446228852773757964117811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4594971803698343952157081 3446228852773757964117811)
            ·
              refine ⟨5169343279160636946176717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3446228852773757964117811 5169343279160636946176717)
              ·
                refine ⟨1938503729685238854816269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5169343279160636946176717 1938503729685238854816269)
                ·
                  refine ⟨726938898631964570556101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1938503729685238854816269 726938898631964570556101)
                  ·
                    refine ⟨136301043493493356979269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 726938898631964570556101 136301043493493356979269)
                    ·
                      refine ⟨25556445655030004433613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 136301043493493356979269 25556445655030004433613)
                      ·
                        rfl

theorem cell23_49771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 4, 4].length) (baseStart_49771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_49771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_49771 prefixEnd_49771 := by exact prefixLift 49771
  have htrace : WordTrace (prefixWord ++ tailWord_49771) baseStart_49771 baseEnd_49771 := by
    simpa [prefixWord, tailWord_49771, baseEnd_49771] using wordTrace_append hprefix tailTrace_49771
  have hstable : (prefixWord ++ tailWord_49771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49771).length < 2 ^ (prefixWord ++ tailWord_49771).sum := by decide
  have hdescent : baseEnd_49771 < baseStart_49771 := by decide
  rcases family_descends (prefixWord ++ tailWord_49771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49775 : List Nat := [1, 1, 2, 1, 3, 2, 2, 1, 6, 2, 2]
def baseStart_49775 : Nat := 118140960795 + 49775 * 2 ^ 59
def prefixEnd_49775 : Nat := 4983230072969 + 3 ^ 40 * 49775 * 2
def baseEnd_49775 : Nat := 25558499577647988783595

theorem tailTrace_49775 : CollatzResearch.WordTrace tailWord_49775 prefixEnd_49775 25558499577647988783595 := by
  unfold tailWord_49775
  simp only [CollatzResearch.WordTrace]
  refine ⟨1815443394681150738318779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1210295596454100492212519 1815443394681150738318779)
  ·
    refine ⟨2723165092021726107478169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1815443394681150738318779 2723165092021726107478169)
    ·
      refine ⟨2042373819016294580608627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2723165092021726107478169 2042373819016294580608627)
      ·
        refine ⟨3063560728524441870912941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2042373819016294580608627 3063560728524441870912941)
        ·
          refine ⟨1148835273196665701592353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3063560728524441870912941 1148835273196665701592353)
          ·
            refine ⟨861626454897499276194265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1148835273196665701592353 861626454897499276194265)
            ·
              refine ⟨646219841173124457145699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 861626454897499276194265 646219841173124457145699)
              ·
                refine ⟨969329761759686685718549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 646219841173124457145699 969329761759686685718549)
                ·
                  refine ⟨45437332582485313393057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 969329761759686685718549 45437332582485313393057)
                  ·
                    refine ⟨34077999436863985044793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45437332582485313393057 34077999436863985044793)
                    ·
                      refine ⟨25558499577647988783595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 34077999436863985044793 25558499577647988783595)
                      ·
                        rfl

theorem cell23_49775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 6, 2, 2].length) (baseStart_49775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_49775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_49775 prefixEnd_49775 := by exact prefixLift 49775
  have htrace : WordTrace (prefixWord ++ tailWord_49775) baseStart_49775 baseEnd_49775 := by
    simpa [prefixWord, tailWord_49775, baseEnd_49775] using wordTrace_append hprefix tailTrace_49775
  have hstable : (prefixWord ++ tailWord_49775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49775).length < 2 ^ (prefixWord ++ tailWord_49775).sum := by decide
  have hdescent : baseEnd_49775 < baseStart_49775 := by decide
  rcases family_descends (prefixWord ++ tailWord_49775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49792 : List Nat := [2, 1, 1, 2, 1, 5, 1, 4, 2, 2, 2]
def baseStart_49792 : Nat := 118140960795 + 49792 * 2 ^ 59
def prefixEnd_49792 : Nat := 4983230072969 + 3 ^ 40 * 49792 * 2
def baseEnd_49792 : Nat := 25567228748774422271017

theorem tailTrace_49792 : CollatzResearch.WordTrace tailWord_49792 prefixEnd_49792 25567228748774422271017 := by
  unfold tailWord_49792
  simp only [CollatzResearch.WordTrace]
  refine ⟨908031717809781320843815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1210708957079708427791753 908031717809781320843815)
  ·
    refine ⟨1362047576714671981265723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 908031717809781320843815 1362047576714671981265723)
    ·
      refine ⟨2043071365072007971898585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1362047576714671981265723 2043071365072007971898585)
      ·
        refine ⟨1532303523804005978923939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2043071365072007971898585 1532303523804005978923939)
        ·
          refine ⟨2298455285706008968385909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1532303523804005978923939 2298455285706008968385909)
          ·
            refine ⟨215480183034938340786179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2298455285706008968385909 215480183034938340786179)
            ·
              refine ⟨323220274552407511179269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215480183034938340786179 323220274552407511179269)
              ·
                refine ⟨60603801478576408346113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 323220274552407511179269 60603801478576408346113)
                ·
                  refine ⟨45452851108932306259585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60603801478576408346113 45452851108932306259585)
                  ·
                    refine ⟨34089638331699229694689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45452851108932306259585 34089638331699229694689)
                    ·
                      refine ⟨25567228748774422271017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 34089638331699229694689 25567228748774422271017)
                      ·
                        rfl

theorem cell23_49792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 4, 2, 2, 2].length) (baseStart_49792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_49792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_49792 prefixEnd_49792 := by exact prefixLift 49792
  have htrace : WordTrace (prefixWord ++ tailWord_49792) baseStart_49792 baseEnd_49792 := by
    simpa [prefixWord, tailWord_49792, baseEnd_49792] using wordTrace_append hprefix tailTrace_49792
  have hstable : (prefixWord ++ tailWord_49792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49792).length < 2 ^ (prefixWord ++ tailWord_49792).sum := by decide
  have hdescent : baseEnd_49792 < baseStart_49792 := by decide
  rcases family_descends (prefixWord ++ tailWord_49792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49801 : List Nat := [1, 2, 1, 1, 4, 1, 1, 1, 2, 1, 8]
def baseStart_49801 : Nat := 118140960795 + 49801 * 2 ^ 59
def prefixEnd_49801 : Nat := 4983230072969 + 3 ^ 40 * 49801 * 2
def baseEnd_49801 : Nat := 25571850074664887058475

theorem tailTrace_49801 : CollatzResearch.WordTrace tailWord_49801 prefixEnd_49801 25571850074664887058475 := by
  unfold tailWord_49801
  simp only [CollatzResearch.WordTrace]
  refine ⟨1816391692586957178765257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1210927795057971452510171 1816391692586957178765257)
  ·
    refine ⟨1362293769440217884073943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1816391692586957178765257 1362293769440217884073943)
    ·
      refine ⟨2043440654160326826110915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1362293769440217884073943 2043440654160326826110915)
      ·
        refine ⟨3065160981240490239166373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2043440654160326826110915 3065160981240490239166373)
        ·
          refine ⟨574717683982591919843695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3065160981240490239166373 574717683982591919843695)
          ·
            refine ⟨862076525973887879765543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 574717683982591919843695 862076525973887879765543)
            ·
              refine ⟨1293114788960831819648315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 862076525973887879765543 1293114788960831819648315)
              ·
                refine ⟨1939672183441247729472473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1293114788960831819648315 1939672183441247729472473)
                ·
                  refine ⟨1454754137580935797104355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1939672183441247729472473 1454754137580935797104355)
                  ·
                    refine ⟨2182131206371403695656533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1454754137580935797104355 2182131206371403695656533)
                    ·
                      refine ⟨25571850074664887058475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 2182131206371403695656533 25571850074664887058475)
                      ·
                        rfl

theorem cell23_49801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 1, 8].length) (baseStart_49801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_49801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_49801 prefixEnd_49801 := by exact prefixLift 49801
  have htrace : WordTrace (prefixWord ++ tailWord_49801) baseStart_49801 baseEnd_49801 := by
    simpa [prefixWord, tailWord_49801, baseEnd_49801] using wordTrace_append hprefix tailTrace_49801
  have hstable : (prefixWord ++ tailWord_49801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49801).length < 2 ^ (prefixWord ++ tailWord_49801).sum := by decide
  have hdescent : baseEnd_49801 < baseStart_49801 := by decide
  rcases family_descends (prefixWord ++ tailWord_49801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49811 : List Nat := [1, 1, 1, 2, 1, 2, 2, 3, 3, 7]
def baseStart_49811 : Nat := 118140960795 + 49811 * 2 ^ 59
def prefixEnd_49811 : Nat := 4983230072969 + 3 ^ 40 * 49811 * 2
def baseEnd_49811 : Nat := 8525661627069949311143

theorem tailTrace_49811 : CollatzResearch.WordTrace tailWord_49811 prefixEnd_49811 8525661627069949311143 := by
  unfold tailWord_49811
  simp only [CollatzResearch.WordTrace]
  refine ⟨1816756422550728886629287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1211170948367152591086191 1816756422550728886629287)
  ·
    refine ⟨2725134633826093329943931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1816756422550728886629287 2725134633826093329943931)
    ·
      refine ⟨4087701950739139994915897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2725134633826093329943931 4087701950739139994915897)
      ·
        refine ⟨3065776463054354996186923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4087701950739139994915897 3065776463054354996186923)
        ·
          refine ⟨4598664694581532494280385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3065776463054354996186923 4598664694581532494280385)
          ·
            refine ⟨3448998520936149370710289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4598664694581532494280385 3448998520936149370710289)
            ·
              refine ⟨2586748890702112028032717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3448998520936149370710289 2586748890702112028032717)
              ·
                refine ⟨970030834013292010512269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2586748890702112028032717 970030834013292010512269)
                ·
                  refine ⟨363761562754984503942101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 970030834013292010512269 363761562754984503942101)
                  ·
                    refine ⟨8525661627069949311143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 363761562754984503942101 8525661627069949311143)
                    ·
                      rfl

theorem cell23_49811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 7].length) (baseStart_49811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_49811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_49811 prefixEnd_49811 := by exact prefixLift 49811
  have htrace : WordTrace (prefixWord ++ tailWord_49811) baseStart_49811 baseEnd_49811 := by
    simpa [prefixWord, tailWord_49811, baseEnd_49811] using wordTrace_append hprefix tailTrace_49811
  have hstable : (prefixWord ++ tailWord_49811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49811).length < 2 ^ (prefixWord ++ tailWord_49811).sum := by decide
  have hdescent : baseEnd_49811 < baseStart_49811 := by decide
  rcases family_descends (prefixWord ++ tailWord_49811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49828 : List Nat := [2, 3, 1, 2, 2, 1, 3, 1, 1, 7]
def baseStart_49828 : Nat := 118140960795 + 49828 * 2 ^ 59
def prefixEnd_49828 : Nat := 4983230072969 + 3 ^ 40 * 49828 * 2
def baseEnd_49828 : Nat := 8528571350778760473617

theorem tailTrace_49828 : CollatzResearch.WordTrace tailWord_49828 prefixEnd_49828 8528571350778760473617 := by
  unfold tailWord_49828
  simp only [CollatzResearch.WordTrace]
  refine ⟨908688231744570394999069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1211584308992760526665425 908688231744570394999069)
  ·
    refine ⟨340758086904213898124651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 908688231744570394999069 340758086904213898124651)
    ·
      refine ⟨511137130356320847186977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340758086904213898124651 511137130356320847186977)
      ·
        refine ⟨383352847767240635390233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 511137130356320847186977 383352847767240635390233)
        ·
          refine ⟨287514635825430476542675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 383352847767240635390233 287514635825430476542675)
          ·
            refine ⟨431271953738145714814013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287514635825430476542675 431271953738145714814013)
            ·
              refine ⟨161726982651804643055255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 431271953738145714814013 161726982651804643055255)
              ·
                refine ⟨242590473977706964582883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161726982651804643055255 242590473977706964582883)
                ·
                  refine ⟨363885710966560446874325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 242590473977706964582883 363885710966560446874325)
                  ·
                    refine ⟨8528571350778760473617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 363885710966560446874325 8528571350778760473617)
                    ·
                      rfl

theorem cell23_49828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 1, 7].length) (baseStart_49828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_49828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_49828 prefixEnd_49828 := by exact prefixLift 49828
  have htrace : WordTrace (prefixWord ++ tailWord_49828) baseStart_49828 baseEnd_49828 := by
    simpa [prefixWord, tailWord_49828, baseEnd_49828] using wordTrace_append hprefix tailTrace_49828
  have hstable : (prefixWord ++ tailWord_49828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49828).length < 2 ^ (prefixWord ++ tailWord_49828).sum := by decide
  have hdescent : baseEnd_49828 < baseStart_49828 := by decide
  rcases family_descends (prefixWord ++ tailWord_49828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49902 : List Nat := [4, 1, 2, 1, 1, 4, 1, 2, 2, 2, 3]
def baseStart_49902 : Nat := 118140960795 + 49902 * 2 ^ 59
def prefixEnd_49902 : Nat := 4983230072969 + 3 ^ 40 * 49902 * 2
def baseEnd_49902 : Nat := 25623711620768991895511

theorem tailTrace_49902 : CollatzResearch.WordTrace tailWord_49902 prefixEnd_49902 25623711620768991895511 := by
  unfold tailWord_49902
  simp only [CollatzResearch.WordTrace]
  refine ⟨227509433152631428523995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1213383643480700952127973 227509433152631428523995)
  ·
    refine ⟨341264149728947142785993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227509433152631428523995 341264149728947142785993)
    ·
      refine ⟨255948112296710357089495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341264149728947142785993 255948112296710357089495)
      ·
        refine ⟨383922168445065535634243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255948112296710357089495 383922168445065535634243)
        ·
          refine ⟨575883252667598303451365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 383922168445065535634243 575883252667598303451365)
          ·
            refine ⟨107978109875174681897131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 575883252667598303451365 107978109875174681897131)
            ·
              refine ⟨161967164812762022845697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107978109875174681897131 161967164812762022845697)
              ·
                refine ⟨121475373609571517134273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161967164812762022845697 121475373609571517134273)
                ·
                  refine ⟨91106530207178637850705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121475373609571517134273 91106530207178637850705)
                  ·
                    refine ⟨68329897655383978388029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 91106530207178637850705 68329897655383978388029)
                    ·
                      refine ⟨25623711620768991895511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 68329897655383978388029 25623711620768991895511)
                      ·
                        rfl

theorem cell23_49902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_49902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_49902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_49902 prefixEnd_49902 := by exact prefixLift 49902
  have htrace : WordTrace (prefixWord ++ tailWord_49902) baseStart_49902 baseEnd_49902 := by
    simpa [prefixWord, tailWord_49902, baseEnd_49902] using wordTrace_append hprefix tailTrace_49902
  have hstable : (prefixWord ++ tailWord_49902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49902).length < 2 ^ (prefixWord ++ tailWord_49902).sum := by decide
  have hdescent : baseEnd_49902 < baseStart_49902 := by decide
  rcases family_descends (prefixWord ++ tailWord_49902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49922 : List Nat := [3, 4, 1, 1, 1, 3, 1, 3, 6]
def baseStart_49922 : Nat := 118140960795 + 49922 * 2 ^ 59
def prefixEnd_49922 : Nat := 4983230072969 + 3 ^ 40 * 49922 * 2
def baseEnd_49922 : Nat := 2848220137095434849491

theorem tailTrace_49922 : CollatzResearch.WordTrace tailWord_49922 prefixEnd_49922 2848220137095434849491 := by
  unfold tailWord_49922
  simp only [CollatzResearch.WordTrace]
  refine ⟨455201231287148710980005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1213869950099063229280013 455201231287148710980005)
  ·
    refine ⟨85350230866340383308751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 455201231287148710980005 85350230866340383308751)
    ·
      refine ⟨128025346299510574963127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85350230866340383308751 128025346299510574963127)
      ·
        refine ⟨192038019449265862444691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128025346299510574963127 192038019449265862444691)
        ·
          refine ⟨288057029173898793667037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192038019449265862444691 288057029173898793667037)
          ·
            refine ⟨108021385940212047625139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 288057029173898793667037 108021385940212047625139)
            ·
              refine ⟨162032078910318071437709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108021385940212047625139 162032078910318071437709)
              ·
                refine ⟨60762029591369276789141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 162032078910318071437709 60762029591369276789141)
                ·
                  refine ⟨2848220137095434849491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 60762029591369276789141 2848220137095434849491)
                  ·
                    rfl

theorem cell23_49922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_49922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_49922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_49922 prefixEnd_49922 := by exact prefixLift 49922
  have htrace : WordTrace (prefixWord ++ tailWord_49922) baseStart_49922 baseEnd_49922 := by
    simpa [prefixWord, tailWord_49922, baseEnd_49922] using wordTrace_append hprefix tailTrace_49922
  have hstable : (prefixWord ++ tailWord_49922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49922).length < 2 ^ (prefixWord ++ tailWord_49922).sum := by decide
  have hdescent : baseEnd_49922 < baseStart_49922 := by decide
  rcases family_descends (prefixWord ++ tailWord_49922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49925 : List Nat := [1, 3, 1, 1, 2, 1, 1, 3, 3, 5, 2]
def baseStart_49925 : Nat := 118140960795 + 49925 * 2 ^ 59
def prefixEnd_49925 : Nat := 4983230072969 + 3 ^ 40 * 49925 * 2
def baseEnd_49925 : Nat := 25635521675822401907905

theorem tailTrace_49925 : CollatzResearch.WordTrace tailWord_49925 prefixEnd_49925 25635521675822401907905 := by
  unfold tailWord_49925
  simp only [CollatzResearch.WordTrace]
  refine ⟨1820914344137726356279229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1213942896091817570852819 1820914344137726356279229)
  ·
    refine ⟨682842879051647383604711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1820914344137726356279229 682842879051647383604711)
    ·
      refine ⟨1024264318577471075407067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 682842879051647383604711 1024264318577471075407067)
      ·
        refine ⟨1536396477866206613110601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1024264318577471075407067 1536396477866206613110601)
        ·
          refine ⟨1152297358399654959832951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1536396477866206613110601 1152297358399654959832951)
          ·
            refine ⟨1728446037599482439749427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1152297358399654959832951 1728446037599482439749427)
            ·
              refine ⟨2592669056399223659624141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1728446037599482439749427 2592669056399223659624141)
              ·
                refine ⟨972250896149708872359053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2592669056399223659624141 972250896149708872359053)
                ·
                  refine ⟨364594086056140827134645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 972250896149708872359053 364594086056140827134645)
                  ·
                    refine ⟨34180695567763202543873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 364594086056140827134645 34180695567763202543873)
                    ·
                      refine ⟨25635521675822401907905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 34180695567763202543873 25635521675822401907905)
                      ·
                        rfl

theorem cell23_49925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 5, 2].length) (baseStart_49925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_49925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_49925 prefixEnd_49925 := by exact prefixLift 49925
  have htrace : WordTrace (prefixWord ++ tailWord_49925) baseStart_49925 baseEnd_49925 := by
    simpa [prefixWord, tailWord_49925, baseEnd_49925] using wordTrace_append hprefix tailTrace_49925
  have hstable : (prefixWord ++ tailWord_49925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49925).length < 2 ^ (prefixWord ++ tailWord_49925).sum := by decide
  have hdescent : baseEnd_49925 < baseStart_49925 := by decide
  rcases family_descends (prefixWord ++ tailWord_49925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49968 : List Nat := [2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 6]
def baseStart_49968 : Nat := 118140960795 + 49968 * 2 ^ 59
def prefixEnd_49968 : Nat := 4983230072969 + 3 ^ 40 * 49968 * 2
def baseEnd_49968 : Nat := 25657601343965733670207

theorem tailTrace_49968 : CollatzResearch.WordTrace tailWord_49968 prefixEnd_49968 25657601343965733670207 := by
  unfold tailWord_49968
  simp only [CollatzResearch.WordTrace]
  refine ⟨911241341490972350047279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1214988455321296466729705 911241341490972350047279)
  ·
    refine ⟨1366862012236458525070919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 911241341490972350047279 1366862012236458525070919)
    ·
      refine ⟨2050293018354687787606379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1366862012236458525070919 2050293018354687787606379)
      ·
        refine ⟨3075439527532031681409569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2050293018354687787606379 3075439527532031681409569)
        ·
          refine ⟨2306579645649023761057177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3075439527532031681409569 2306579645649023761057177)
          ·
            refine ⟨1729934734236767820792883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2306579645649023761057177 1729934734236767820792883)
            ·
              refine ⟨2594902101355151731189325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1729934734236767820792883 2594902101355151731189325)
              ·
                refine ⟨973088288008181899195997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2594902101355151731189325 973088288008181899195997)
                ·
                  refine ⟨364908108003068212198499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 973088288008181899195997 364908108003068212198499)
                  ·
                    refine ⟨547362162004602318297749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 364908108003068212198499 547362162004602318297749)
                    ·
                      refine ⟨25657601343965733670207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 547362162004602318297749 25657601343965733670207)
                      ·
                        rfl

theorem cell23_49968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 6].length) (baseStart_49968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_49968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_49968 prefixEnd_49968 := by exact prefixLift 49968
  have htrace : WordTrace (prefixWord ++ tailWord_49968) baseStart_49968 baseEnd_49968 := by
    simpa [prefixWord, tailWord_49968, baseEnd_49968] using wordTrace_append hprefix tailTrace_49968
  have hstable : (prefixWord ++ tailWord_49968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49968).length < 2 ^ (prefixWord ++ tailWord_49968).sum := by decide
  have hdescent : baseEnd_49968 < baseStart_49968 := by decide
  rcases family_descends (prefixWord ++ tailWord_49968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49975 : List Nat := [1, 1, 3, 1, 2, 1, 3, 1, 5, 2, 3]
def baseStart_49975 : Nat := 118140960795 + 49975 * 2 ^ 59
def prefixEnd_49975 : Nat := 4983230072969 + 3 ^ 40 * 49975 * 2
def baseEnd_49975 : Nat := 25661195708547206282675

theorem tailTrace_49975 : CollatzResearch.WordTrace tailWord_49975 prefixEnd_49975 25661195708547206282675 := by
  unfold tailWord_49975
  simp only [CollatzResearch.WordTrace]
  refine ⟨1822737993956584895599379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1215158662637723263732919 1822737993956584895599379)
  ·
    refine ⟨2734106990934877343399069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1822737993956584895599379 2734106990934877343399069)
    ·
      refine ⟨1025290121600579003774651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2734106990934877343399069 1025290121600579003774651)
      ·
        refine ⟨1537935182400868505661977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1025290121600579003774651 1537935182400868505661977)
        ·
          refine ⟨1153451386800651379246483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1537935182400868505661977 1153451386800651379246483)
          ·
            refine ⟨1730177080200977068869725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1153451386800651379246483 1730177080200977068869725)
            ·
              refine ⟨648816405075366400826147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1730177080200977068869725 648816405075366400826147)
              ·
                refine ⟨973224607613049601239221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 648816405075366400826147 973224607613049601239221)
                ·
                  refine ⟨91239806963723400116177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 973224607613049601239221 91239806963723400116177)
                  ·
                    refine ⟨68429855222792550087133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 91239806963723400116177 68429855222792550087133)
                    ·
                      refine ⟨25661195708547206282675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 68429855222792550087133 25661195708547206282675)
                      ·
                        rfl

theorem cell23_49975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 5, 2, 3].length) (baseStart_49975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_49975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_49975 prefixEnd_49975 := by exact prefixLift 49975
  have htrace : WordTrace (prefixWord ++ tailWord_49975) baseStart_49975 baseEnd_49975 := by
    simpa [prefixWord, tailWord_49975, baseEnd_49975] using wordTrace_append hprefix tailTrace_49975
  have hstable : (prefixWord ++ tailWord_49975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49975).length < 2 ^ (prefixWord ++ tailWord_49975).sum := by decide
  have hdescent : baseEnd_49975 < baseStart_49975 := by decide
  rcases family_descends (prefixWord ++ tailWord_49975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49992 : List Nat := [2, 1, 3, 1, 1, 3, 2, 4, 1, 2, 3]
def baseStart_49992 : Nat := 118140960795 + 49992 * 2 ^ 59
def prefixEnd_49992 : Nat := 4983230072969 + 3 ^ 40 * 49992 * 2
def baseEnd_49992 : Nat := 25669924879673639770097

theorem tailTrace_49992 : CollatzResearch.WordTrace tailWord_49992 prefixEnd_49992 25669924879673639770097 := by
  unfold tailWord_49992
  simp only [CollatzResearch.WordTrace]
  refine ⟨911679017447498399484115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1215572023263331199312153 911679017447498399484115)
  ·
    refine ⟨1367518526171247599226173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 911679017447498399484115 1367518526171247599226173)
    ·
      refine ⟨512819447314217849709815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1367518526171247599226173 512819447314217849709815)
      ·
        refine ⟨769229170971326774564723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 512819447314217849709815 769229170971326774564723)
        ·
          refine ⟨1153843756456990161847085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 769229170971326774564723 1153843756456990161847085)
          ·
            refine ⟨432691408671371310692657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1153843756456990161847085 432691408671371310692657)
            ·
              refine ⟨324518556503528483019493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 432691408671371310692657 324518556503528483019493)
              ·
                refine ⟨60847229344411590566155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 324518556503528483019493 60847229344411590566155)
                ·
                  refine ⟨91270844016617385849233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60847229344411590566155 91270844016617385849233)
                  ·
                    refine ⟨68453133012463039386925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 91270844016617385849233 68453133012463039386925)
                    ·
                      refine ⟨25669924879673639770097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 68453133012463039386925 25669924879673639770097)
                      ·
                        rfl

theorem cell23_49992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 4, 1, 2, 3].length) (baseStart_49992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_49992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_49992 prefixEnd_49992 := by exact prefixLift 49992
  have htrace : WordTrace (prefixWord ++ tailWord_49992) baseStart_49992 baseEnd_49992 := by
    simpa [prefixWord, tailWord_49992, baseEnd_49992] using wordTrace_append hprefix tailTrace_49992
  have hstable : (prefixWord ++ tailWord_49992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49992).length < 2 ^ (prefixWord ++ tailWord_49992).sum := by decide
  have hdescent : baseEnd_49992 < baseStart_49992 := by decide
  rcases family_descends (prefixWord ++ tailWord_49992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50009 : List Nat := [1, 2, 1, 2, 2, 4, 4, 1, 1, 2, 3]
def baseStart_50009 : Nat := 118140960795 + 50009 * 2 ^ 59
def prefixEnd_50009 : Nat := 4983230072969 + 3 ^ 40 * 50009 * 2
def baseEnd_50009 : Nat := 25678654050800073257519

theorem tailTrace_50009 : CollatzResearch.WordTrace tailWord_50009 prefixEnd_50009 25678654050800073257519 := by
  unfold tailWord_50009
  simp only [CollatzResearch.WordTrace]
  refine ⟨1823978075833408702337081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1215985383888939134891387 1823978075833408702337081)
  ·
    refine ⟨1367983556875056526752811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1823978075833408702337081 1367983556875056526752811)
    ·
      refine ⟨2051975335312584790129217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1367983556875056526752811 2051975335312584790129217)
      ·
        refine ⟨1538981501484438592596913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2051975335312584790129217 1538981501484438592596913)
        ·
          refine ⟨1154236126113328944447685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1538981501484438592596913 1154236126113328944447685)
          ·
            refine ⟨216419273646249177083941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1154236126113328944447685 216419273646249177083941)
            ·
              refine ⟨40578613808671720703239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 216419273646249177083941 40578613808671720703239)
              ·
                refine ⟨60867920713007581054859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40578613808671720703239 60867920713007581054859)
                ·
                  refine ⟨91301881069511371582289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60867920713007581054859 91301881069511371582289)
                  ·
                    refine ⟨68476410802133528686717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 91301881069511371582289 68476410802133528686717)
                    ·
                      refine ⟨25678654050800073257519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 68476410802133528686717 25678654050800073257519)
                      ·
                        rfl

theorem cell23_50009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 4, 1, 1, 2, 3].length) (baseStart_50009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_50009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_50009 prefixEnd_50009 := by exact prefixLift 50009
  have htrace : WordTrace (prefixWord ++ tailWord_50009) baseStart_50009 baseEnd_50009 := by
    simpa [prefixWord, tailWord_50009, baseEnd_50009] using wordTrace_append hprefix tailTrace_50009
  have hstable : (prefixWord ++ tailWord_50009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50009).length < 2 ^ (prefixWord ++ tailWord_50009).sum := by decide
  have hdescent : baseEnd_50009 < baseStart_50009 := by decide
  rcases family_descends (prefixWord ++ tailWord_50009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50032 : List Nat := [2, 1, 1, 1, 4, 1, 2, 1, 5, 3, 2]
def baseStart_50032 : Nat := 118140960795 + 50032 * 2 ^ 59
def prefixEnd_50032 : Nat := 4983230072969 + 3 ^ 40 * 50032 * 2
def baseEnd_50032 : Nat := 25690464105853483269913

theorem tailTrace_50032 : CollatzResearch.WordTrace tailWord_50032 prefixEnd_50032 25690464105853483269913 := by
  unfold tailWord_50032
  simp only [CollatzResearch.WordTrace]
  refine ⟨912408477375041815212175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1216544636500055753616233 912408477375041815212175)
  ·
    refine ⟨1368612716062562722818263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 912408477375041815212175 1368612716062562722818263)
    ·
      refine ⟨2052919074093844084227395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1368612716062562722818263 2052919074093844084227395)
      ·
        refine ⟨3079378611140766126341093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2052919074093844084227395 3079378611140766126341093)
        ·
          refine ⟨577383489588893648688955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3079378611140766126341093 577383489588893648688955)
          ·
            refine ⟨866075234383340473033433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 577383489588893648688955 866075234383340473033433)
            ·
              refine ⟨649556425787505354775075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 866075234383340473033433 649556425787505354775075)
              ·
                refine ⟨974334638681258032162613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 649556425787505354775075 974334638681258032162613)
                ·
                  refine ⟨91343872376367940515245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 974334638681258032162613 91343872376367940515245)
                  ·
                    refine ⟨34253952141137977693217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 91343872376367940515245 34253952141137977693217)
                    ·
                      refine ⟨25690464105853483269913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 34253952141137977693217 25690464105853483269913)
                      ·
                        rfl

theorem cell23_50032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 5, 3, 2].length) (baseStart_50032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_50032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_50032 prefixEnd_50032 := by exact prefixLift 50032
  have htrace : WordTrace (prefixWord ++ tailWord_50032) baseStart_50032 baseEnd_50032 := by
    simpa [prefixWord, tailWord_50032, baseEnd_50032] using wordTrace_append hprefix tailTrace_50032
  have hstable : (prefixWord ++ tailWord_50032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50032).length < 2 ^ (prefixWord ++ tailWord_50032).sum := by decide
  have hdescent : baseEnd_50032 < baseStart_50032 := by decide
  rcases family_descends (prefixWord ++ tailWord_50032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50045 : List Nat := [1, 4, 1, 1, 2, 1, 2, 2, 2, 3, 4]
def baseStart_50045 : Nat := 118140960795 + 50045 * 2 ^ 59
def prefixEnd_50045 : Nat := 4983230072969 + 3 ^ 40 * 50045 * 2
def baseEnd_50045 : Nat := 25697139354361932407353

theorem tailTrace_50045 : CollatzResearch.WordTrace tailWord_50045 prefixEnd_50045 25697139354361932407353 := by
  unfold tailWord_50045
  simp only [CollatzResearch.WordTrace]
  refine ⟨1825291103702986850647589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1216860735801991233765059 1825291103702986850647589)
  ·
    refine ⟨342242081944310034496423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1825291103702986850647589 342242081944310034496423)
    ·
      refine ⟨513363122916465051744635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342242081944310034496423 513363122916465051744635)
      ·
        refine ⟨770044684374697577616953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 513363122916465051744635 770044684374697577616953)
        ·
          refine ⟨577533513281023183212715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 770044684374697577616953 577533513281023183212715)
          ·
            refine ⟨866300269921534774819073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 577533513281023183212715 866300269921534774819073)
            ·
              refine ⟨649725202441151081114305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 866300269921534774819073 649725202441151081114305)
              ·
                refine ⟨487293901830863310835729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 649725202441151081114305 487293901830863310835729)
                ·
                  refine ⟨365470426373147483126797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 487293901830863310835729 365470426373147483126797)
                  ·
                    refine ⟨137051409889930306172549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 365470426373147483126797 137051409889930306172549)
                    ·
                      refine ⟨25697139354361932407353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 137051409889930306172549 25697139354361932407353)
                      ·
                        rfl

theorem cell23_50045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_50045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_50045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_50045 prefixEnd_50045 := by exact prefixLift 50045
  have htrace : WordTrace (prefixWord ++ tailWord_50045) baseStart_50045 baseEnd_50045 := by
    simpa [prefixWord, tailWord_50045, baseEnd_50045] using wordTrace_append hprefix tailTrace_50045
  have hstable : (prefixWord ++ tailWord_50045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50045).length < 2 ^ (prefixWord ++ tailWord_50045).sum := by decide
  have hdescent : baseEnd_50045 < baseStart_50045 := by decide
  rcases family_descends (prefixWord ++ tailWord_50045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50046 : List Nat := [4, 2, 3, 1, 2, 2, 2, 7]
def baseStart_50046 : Nat := 118140960795 + 50046 * 2 ^ 59
def prefixEnd_50046 : Nat := 4983230072969 + 3 ^ 40 * 50046 * 2
def baseEnd_50046 : Nat := 951764919815423277587

theorem tailTrace_50046 : CollatzResearch.WordTrace tailWord_50046 prefixEnd_50046 951764919815423277587 := by
  unfold tailWord_50046
  simp only [CollatzResearch.WordTrace]
  refine ⟨228165947087420502679249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1216885051132909347622661 228165947087420502679249)
  ·
    refine ⟨171124460315565377009437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228165947087420502679249 171124460315565377009437)
    ·
      refine ⟨64171672618337016378539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171124460315565377009437 64171672618337016378539)
      ·
        refine ⟨96257508927505524567809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64171672618337016378539 96257508927505524567809)
        ·
          refine ⟨72193131695629143425857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96257508927505524567809 72193131695629143425857)
          ·
            refine ⟨54144848771721857569393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72193131695629143425857 54144848771721857569393)
            ·
              refine ⟨40608636578791393177045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54144848771721857569393 40608636578791393177045)
              ·
                refine ⟨951764919815423277587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 40608636578791393177045 951764919815423277587)
                ·
                  rfl

theorem cell23_50046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 2, 7].length) (baseStart_50046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_50046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_50046 prefixEnd_50046 := by exact prefixLift 50046
  have htrace : WordTrace (prefixWord ++ tailWord_50046) baseStart_50046 baseEnd_50046 := by
    simpa [prefixWord, tailWord_50046, baseEnd_50046] using wordTrace_append hprefix tailTrace_50046
  have hstable : (prefixWord ++ tailWord_50046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50046).length < 2 ^ (prefixWord ++ tailWord_50046).sum := by decide
  have hdescent : baseEnd_50046 < baseStart_50046 := by decide
  rcases family_descends (prefixWord ++ tailWord_50046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50065 : List Nat := [1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 3]
def baseStart_50065 : Nat := 118140960795 + 50065 * 2 ^ 59
def prefixEnd_50065 : Nat := 4983230072969 + 3 ^ 40 * 50065 * 2
def baseEnd_50065 : Nat := 25707408967451854157261

theorem tailTrace_50065 : CollatzResearch.WordTrace tailWord_50065 prefixEnd_50065 25707408967451854157261 := by
  unfold tailWord_50065
  simp only [CollatzResearch.WordTrace]
  refine ⟨1826020563630530266375649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1217347042420353510917099 1826020563630530266375649)
  ·
    refine ⟨1369515422722897699781737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1826020563630530266375649 1369515422722897699781737)
    ·
      refine ⟨1027136567042173274836303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1369515422722897699781737 1027136567042173274836303)
      ·
        refine ⟨1540704850563259912254455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1027136567042173274836303 1540704850563259912254455)
        ·
          refine ⟨2311057275844889868381683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1540704850563259912254455 2311057275844889868381683)
          ·
            refine ⟨3466585913767334802572525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2311057275844889868381683 3466585913767334802572525)
            ·
              refine ⟨1299969717662750550964697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3466585913767334802572525 1299969717662750550964697)
              ·
                refine ⟨974977288247062913223523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1299969717662750550964697 974977288247062913223523)
                ·
                  refine ⟨1462465932370594369835285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 974977288247062913223523 1462465932370594369835285)
                  ·
                    refine ⟨68553090579871611086029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1462465932370594369835285 68553090579871611086029)
                    ·
                      refine ⟨25707408967451854157261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 68553090579871611086029 25707408967451854157261)
                      ·
                        rfl

theorem cell23_50065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 3].length) (baseStart_50065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_50065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_50065 prefixEnd_50065 := by exact prefixLift 50065
  have htrace : WordTrace (prefixWord ++ tailWord_50065) baseStart_50065 baseEnd_50065 := by
    simpa [prefixWord, tailWord_50065, baseEnd_50065] using wordTrace_append hprefix tailTrace_50065
  have hstable : (prefixWord ++ tailWord_50065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50065).length < 2 ^ (prefixWord ++ tailWord_50065).sum := by decide
  have hdescent : baseEnd_50065 < baseStart_50065 := by decide
  rcases family_descends (prefixWord ++ tailWord_50065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50100 : List Nat := [2, 5, 2, 1, 1, 3, 1, 2, 1, 3, 2]
def baseStart_50100 : Nat := 118140960795 + 50100 * 2 ^ 59
def prefixEnd_50100 : Nat := 4983230072969 + 3 ^ 40 * 50100 * 2
def baseEnd_50100 : Nat := 25725380790359217219601

theorem tailTrace_50100 : CollatzResearch.WordTrace tailWord_50100 prefixEnd_50100 25725380790359217219601 := by
  unfold tailWord_50100
  simp only [CollatzResearch.WordTrace]
  refine ⟨913648559251865621949877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1218198079002487495933169 913648559251865621949877)
  ·
    refine ⟨85654552429862402057801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 913648559251865621949877 85654552429862402057801)
    ·
      refine ⟨64240914322396801543351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85654552429862402057801 64240914322396801543351)
      ·
        refine ⟨96361371483595202315027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64240914322396801543351 96361371483595202315027)
        ·
          refine ⟨144542057225392803472541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96361371483595202315027 144542057225392803472541)
          ·
            refine ⟨54203271459522301302203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144542057225392803472541 54203271459522301302203)
            ·
              refine ⟨81304907189283451953305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54203271459522301302203 81304907189283451953305)
              ·
                refine ⟨60978680391962588964979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81304907189283451953305 60978680391962588964979)
                ·
                  refine ⟨91468020587943883447469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60978680391962588964979 91468020587943883447469)
                  ·
                    refine ⟨34300507720478956292801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 91468020587943883447469 34300507720478956292801)
                    ·
                      refine ⟨25725380790359217219601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 34300507720478956292801 25725380790359217219601)
                      ·
                        rfl

theorem cell23_50100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_50100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_50100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_50100 prefixEnd_50100 := by exact prefixLift 50100
  have htrace : WordTrace (prefixWord ++ tailWord_50100) baseStart_50100 baseEnd_50100 := by
    simpa [prefixWord, tailWord_50100, baseEnd_50100] using wordTrace_append hprefix tailTrace_50100
  have hstable : (prefixWord ++ tailWord_50100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50100).length < 2 ^ (prefixWord ++ tailWord_50100).sum := by decide
  have hdescent : baseEnd_50100 < baseStart_50100 := by decide
  rcases family_descends (prefixWord ++ tailWord_50100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50115 : List Nat := [1, 1, 1, 3, 1, 1, 2, 2, 6, 5]
def baseStart_50115 : Nat := 118140960795 + 50115 * 2 ^ 59
def prefixEnd_50115 : Nat := 4983230072969 + 3 ^ 40 * 50115 * 2
def baseEnd_50115 : Nat := 8577694333392219510677

theorem tailTrace_50115 : CollatzResearch.WordTrace tailWord_50115 prefixEnd_50115 8577694333392219510677 := by
  unfold tailWord_50115
  simp only [CollatzResearch.WordTrace]
  refine ⟨1827844213449388805695799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1218562808966259203797199 1827844213449388805695799)
  ·
    refine ⟨2741766320174083208543699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1827844213449388805695799 2741766320174083208543699)
    ·
      refine ⟨4112649480261124812815549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2741766320174083208543699 4112649480261124812815549)
      ·
        refine ⟨1542243555097921804805831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4112649480261124812815549 1542243555097921804805831)
        ·
          refine ⟨2313365332646882707208747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1542243555097921804805831 2313365332646882707208747)
          ·
            refine ⟨3470047998970324060813121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2313365332646882707208747 3470047998970324060813121)
            ·
              refine ⟨2602535999227743045609841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3470047998970324060813121 2602535999227743045609841)
              ·
                refine ⟨1951901999420807284207381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2602535999227743045609841 1951901999420807284207381)
                ·
                  refine ⟨91495406222850341447221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1951901999420807284207381 91495406222850341447221)
                  ·
                    refine ⟨8577694333392219510677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 91495406222850341447221 8577694333392219510677)
                    ·
                      rfl

theorem cell23_50115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 6, 5].length) (baseStart_50115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_50115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_50115 prefixEnd_50115 := by exact prefixLift 50115
  have htrace : WordTrace (prefixWord ++ tailWord_50115) baseStart_50115 baseEnd_50115 := by
    simpa [prefixWord, tailWord_50115, baseEnd_50115] using wordTrace_append hprefix tailTrace_50115
  have hstable : (prefixWord ++ tailWord_50115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50115).length < 2 ^ (prefixWord ++ tailWord_50115).sum := by decide
  have hdescent : baseEnd_50115 < baseStart_50115 := by decide
  rcases family_descends (prefixWord ++ tailWord_50115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50136 : List Nat := [2, 1, 2, 2, 2, 5, 2, 2, 5]
def baseStart_50136 : Nat := 118140960795 + 50136 * 2 ^ 59
def prefixEnd_50136 : Nat := 4983230072969 + 3 ^ 40 * 50136 * 2
def baseEnd_50136 : Nat := 2860429565991230707715

theorem tailTrace_50136 : CollatzResearch.WordTrace tailWord_50136 prefixEnd_50136 2860429565991230707715 := by
  unfold tailWord_50136
  simp only [CollatzResearch.WordTrace]
  refine ⟨914305073186654696105131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1219073430915539594806841 914305073186654696105131)
  ·
    refine ⟨1371457609779982044157697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 914305073186654696105131 1371457609779982044157697)
    ·
      refine ⟨1028593207334986533118273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1371457609779982044157697 1028593207334986533118273)
      ·
        refine ⟨771444905501239899838705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1028593207334986533118273 771444905501239899838705)
        ·
          refine ⟨578583679125929924879029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 771444905501239899838705 578583679125929924879029)
          ·
            refine ⟨54242219918055930457409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 578583679125929924879029 54242219918055930457409)
            ·
              refine ⟨40681664938541947843057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54242219918055930457409 40681664938541947843057)
              ·
                refine ⟨30511248703906460882293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40681664938541947843057 30511248703906460882293)
                ·
                  refine ⟨2860429565991230707715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30511248703906460882293 2860429565991230707715)
                  ·
                    rfl

theorem cell23_50136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 2, 2, 5].length) (baseStart_50136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_50136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_50136 prefixEnd_50136 := by exact prefixLift 50136
  have htrace : WordTrace (prefixWord ++ tailWord_50136) baseStart_50136 baseEnd_50136 := by
    simpa [prefixWord, tailWord_50136, baseEnd_50136] using wordTrace_append hprefix tailTrace_50136
  have hstable : (prefixWord ++ tailWord_50136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50136).length < 2 ^ (prefixWord ++ tailWord_50136).sum := by decide
  have hdescent : baseEnd_50136 < baseStart_50136 := by decide
  rcases family_descends (prefixWord ++ tailWord_50136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50145 : List Nat := [1, 2, 3, 1, 2, 1, 1, 2, 2, 8]
def baseStart_50145 : Nat := 118140960795 + 50145 * 2 ^ 59
def prefixEnd_50145 : Nat := 4983230072969 + 3 ^ 40 * 50145 * 2
def baseEnd_50145 : Nat := 8582829139937180385631

theorem tailTrace_50145 : CollatzResearch.WordTrace tailWord_50145 prefixEnd_50145 8582829139937180385631 := by
  unfold tailWord_50145
  simp only [CollatzResearch.WordTrace]
  refine ⟨1828938403340703929287889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1219292268893802619525259 1828938403340703929287889)
  ·
    refine ⟨1371703802505527946965917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1828938403340703929287889 1371703802505527946965917)
    ·
      refine ⟨514388925939572980112219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1371703802505527946965917 514388925939572980112219)
      ·
        refine ⟨771583388909359470168329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 514388925939572980112219 771583388909359470168329)
        ·
          refine ⟨578687541682019602626247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 771583388909359470168329 578687541682019602626247)
          ·
            refine ⟨868031312523029403939371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 578687541682019602626247 868031312523029403939371)
            ·
              refine ⟨1302046968784544105909057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 868031312523029403939371 1302046968784544105909057)
              ·
                refine ⟨976535226588408079431793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1302046968784544105909057 976535226588408079431793)
                ·
                  refine ⟨732401419941306059573845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 976535226588408079431793 732401419941306059573845)
                  ·
                    refine ⟨8582829139937180385631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 732401419941306059573845 8582829139937180385631)
                    ·
                      rfl

theorem cell23_50145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 8].length) (baseStart_50145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_50145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_50145 prefixEnd_50145 := by exact prefixLift 50145
  have htrace : WordTrace (prefixWord ++ tailWord_50145) baseStart_50145 baseEnd_50145 := by
    simpa [prefixWord, tailWord_50145, baseEnd_50145] using wordTrace_append hprefix tailTrace_50145
  have hstable : (prefixWord ++ tailWord_50145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50145).length < 2 ^ (prefixWord ++ tailWord_50145).sum := by decide
  have hdescent : baseEnd_50145 < baseStart_50145 := by decide
  rcases family_descends (prefixWord ++ tailWord_50145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50146 : List Nat := [3, 3, 3, 1, 1, 2, 1, 1, 2, 3, 3]
def baseStart_50146 : Nat := 118140960795 + 50146 * 2 ^ 59
def prefixEnd_50146 : Nat := 4983230072969 + 3 ^ 40 * 50146 * 2
def baseEnd_50146 : Nat := 25749000900466037244389

theorem tailTrace_50146 : CollatzResearch.WordTrace tailWord_50146 prefixEnd_50146 25749000900466037244389 := by
  unfold tailWord_50146
  simp only [CollatzResearch.WordTrace]
  refine ⟨457243719084270275018573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1219316584224720733382861 457243719084270275018573)
  ·
    refine ⟨171466394656601353131965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 457243719084270275018573 171466394656601353131965)
    ·
      refine ⟨64299897996225507424487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171466394656601353131965 64299897996225507424487)
      ·
        refine ⟨96449846994338261136731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64299897996225507424487 96449846994338261136731)
        ·
          refine ⟨144674770491507391705097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96449846994338261136731 144674770491507391705097)
          ·
            refine ⟨108506077868630543778823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144674770491507391705097 108506077868630543778823)
            ·
              refine ⟨162759116802945815668235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108506077868630543778823 162759116802945815668235)
              ·
                refine ⟨244138675204418723502353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162759116802945815668235 244138675204418723502353)
                ·
                  refine ⟨183104006403314042626765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 244138675204418723502353 183104006403314042626765)
                  ·
                    refine ⟨68664002401242765985037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 183104006403314042626765 68664002401242765985037)
                    ·
                      refine ⟨25749000900466037244389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 68664002401242765985037 25749000900466037244389)
                      ·
                        rfl

theorem cell23_50146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_50146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_50146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_50146 prefixEnd_50146 := by exact prefixLift 50146
  have htrace : WordTrace (prefixWord ++ tailWord_50146) baseStart_50146 baseEnd_50146 := by
    simpa [prefixWord, tailWord_50146, baseEnd_50146] using wordTrace_append hprefix tailTrace_50146
  have hstable : (prefixWord ++ tailWord_50146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50146).length < 2 ^ (prefixWord ++ tailWord_50146).sum := by decide
  have hdescent : baseEnd_50146 < baseStart_50146 := by decide
  rcases family_descends (prefixWord ++ tailWord_50146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50152 : List Nat := [2, 1, 4, 1, 1, 1, 2, 2, 4, 1, 4]
def baseStart_50152 : Nat := 118140960795 + 50152 * 2 ^ 59
def prefixEnd_50152 : Nat := 4983230072969 + 3 ^ 40 * 50152 * 2
def baseEnd_50152 : Nat := 25752081784393013769361

theorem tailTrace_50152 : CollatzResearch.WordTrace tailWord_50152 prefixEnd_50152 25752081784393013769361 := by
  unfold tailWord_50152
  simp only [CollatzResearch.WordTrace]
  refine ⟨914596857157672062396355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1219462476210229416528473 914596857157672062396355)
  ·
    refine ⟨1371895285736508093594533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 914596857157672062396355 1371895285736508093594533)
    ·
      refine ⟨257230366075595267548975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1371895285736508093594533 257230366075595267548975)
      ·
        refine ⟨385845549113392901323463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257230366075595267548975 385845549113392901323463)
        ·
          refine ⟨578768323670089351985195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385845549113392901323463 578768323670089351985195)
          ·
            refine ⟨868152485505134027977793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 578768323670089351985195 868152485505134027977793)
            ·
              refine ⟨651114364128850520983345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 868152485505134027977793 651114364128850520983345)
              ·
                refine ⟨488335773096637890737509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 651114364128850520983345 488335773096637890737509)
                ·
                  refine ⟨91562957455619604513283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 488335773096637890737509 91562957455619604513283)
                  ·
                    refine ⟨137344436183429406769925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 91562957455619604513283 137344436183429406769925)
                    ·
                      refine ⟨25752081784393013769361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 137344436183429406769925 25752081784393013769361)
                      ·
                        rfl

theorem cell23_50152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_50152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_50152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_50152 prefixEnd_50152 := by exact prefixLift 50152
  have htrace : WordTrace (prefixWord ++ tailWord_50152) baseStart_50152 baseEnd_50152 := by
    simpa [prefixWord, tailWord_50152, baseEnd_50152] using wordTrace_append hprefix tailTrace_50152
  have hstable : (prefixWord ++ tailWord_50152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50152).length < 2 ^ (prefixWord ++ tailWord_50152).sum := by decide
  have hdescent : baseEnd_50152 < baseStart_50152 := by decide
  rcases family_descends (prefixWord ++ tailWord_50152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50166 : List Nat := [5, 1, 1, 1, 3, 3, 1, 1, 2, 5]
def baseStart_50166 : Nat := 118140960795 + 50166 * 2 ^ 59
def prefixEnd_50166 : Nat := 4983230072969 + 3 ^ 40 * 50166 * 2
def baseEnd_50166 : Nat := 8586423504518652998099

theorem tailTrace_50166 : CollatzResearch.WordTrace tailWord_50166 prefixEnd_50166 8586423504518652998099 := by
  unfold tailWord_50166
  simp only [CollatzResearch.WordTrace]
  refine ⟨114356521016539032237647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1219802890843083010534901 114356521016539032237647)
  ·
    refine ⟨171534781524808548356471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114356521016539032237647 171534781524808548356471)
    ·
      refine ⟨257302172287212822534707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171534781524808548356471 257302172287212822534707)
      ·
        refine ⟨385953258430819233802061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257302172287212822534707 385953258430819233802061)
        ·
          refine ⟨144732471911557212675773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 385953258430819233802061 144732471911557212675773)
          ·
            refine ⟨54274676966833954753415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144732471911557212675773 54274676966833954753415)
            ·
              refine ⟨81412015450250932130123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54274676966833954753415 81412015450250932130123)
              ·
                refine ⟨122118023175376398195185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81412015450250932130123 122118023175376398195185)
                ·
                  refine ⟨91588517381532298646389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122118023175376398195185 91588517381532298646389)
                  ·
                    refine ⟨8586423504518652998099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 91588517381532298646389 8586423504518652998099)
                    ·
                      rfl

theorem cell23_50166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_50166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_50166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_50166 prefixEnd_50166 := by exact prefixLift 50166
  have htrace : WordTrace (prefixWord ++ tailWord_50166) baseStart_50166 baseEnd_50166 := by
    simpa [prefixWord, tailWord_50166, baseEnd_50166] using wordTrace_append hprefix tailTrace_50166
  have hstable : (prefixWord ++ tailWord_50166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50166).length < 2 ^ (prefixWord ++ tailWord_50166).sum := by decide
  have hdescent : baseEnd_50166 < baseStart_50166 := by decide
  rcases family_descends (prefixWord ++ tailWord_50166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50219 : List Nat := [1, 1, 1, 1, 2, 1, 5, 4, 3, 1, 3]
def baseStart_50219 : Nat := 118140960795 + 50219 * 2 ^ 59
def prefixEnd_50219 : Nat := 4983230072969 + 3 ^ 40 * 50219 * 2
def baseEnd_50219 : Nat := 25786484988244251631553

theorem tailTrace_50219 : CollatzResearch.WordTrace tailWord_50219 prefixEnd_50219 25786484988244251631553 := by
  unfold tailWord_50219
  simp only [CollatzResearch.WordTrace]
  refine ⟨1831637405072614567481711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1221091603381743044987807 1831637405072614567481711)
  ·
    refine ⟨2747456107608921851222567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1831637405072614567481711 2747456107608921851222567)
    ·
      refine ⟨4121184161413382776833851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2747456107608921851222567 4121184161413382776833851)
      ·
        refine ⟨6181776242120074165250777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4121184161413382776833851 6181776242120074165250777)
        ·
          refine ⟨4636332181590055623938083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6181776242120074165250777 4636332181590055623938083)
          ·
            refine ⟨6954498272385083435907125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4636332181590055623938083 6954498272385083435907125)
            ·
              refine ⟨651984213036101572116293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6954498272385083435907125 651984213036101572116293)
              ·
                refine ⟨122247039944269044771805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 651984213036101572116293 122247039944269044771805)
                ·
                  refine ⟨45842639979100891789427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122247039944269044771805 45842639979100891789427)
                  ·
                    refine ⟨68763959968651337684141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45842639979100891789427 68763959968651337684141)
                    ·
                      refine ⟨25786484988244251631553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 68763959968651337684141 25786484988244251631553)
                      ·
                        rfl

theorem cell23_50219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 4, 3, 1, 3].length) (baseStart_50219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_50219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_50219 prefixEnd_50219 := by exact prefixLift 50219
  have htrace : WordTrace (prefixWord ++ tailWord_50219) baseStart_50219 baseEnd_50219 := by
    simpa [prefixWord, tailWord_50219, baseEnd_50219] using wordTrace_append hprefix tailTrace_50219
  have hstable : (prefixWord ++ tailWord_50219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50219).length < 2 ^ (prefixWord ++ tailWord_50219).sum := by decide
  have hdescent : baseEnd_50219 < baseStart_50219 := by decide
  rcases family_descends (prefixWord ++ tailWord_50219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50230 : List Nat := [5, 1, 2, 1, 1, 4, 1, 3, 1, 4]
def baseStart_50230 : Nat := 118140960795 + 50230 * 2 ^ 59
def prefixEnd_50230 : Nat := 4983230072969 + 3 ^ 40 * 50230 * 2
def baseEnd_50230 : Nat := 8597377758481236198001

theorem tailTrace_50230 : CollatzResearch.WordTrace tailWord_50230 prefixEnd_50230 8597377758481236198001 := by
  unfold tailWord_50230
  simp only [CollatzResearch.WordTrace]
  refine ⟨114502413002047715383259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1221359072021842297421429 114502413002047715383259)
  ·
    refine ⟨171753619503071573074889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114502413002047715383259 171753619503071573074889)
    ·
      refine ⟨128815214627303679806167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171753619503071573074889 128815214627303679806167)
      ·
        refine ⟨193222821940955519709251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128815214627303679806167 193222821940955519709251)
        ·
          refine ⟨289834232911433279563877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193222821940955519709251 289834232911433279563877)
          ·
            refine ⟨54343918670893739918227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 289834232911433279563877 54343918670893739918227)
            ·
              refine ⟨81515878006340609877341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54343918670893739918227 81515878006340609877341)
              ·
                refine ⟨30568454252377728704003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81515878006340609877341 30568454252377728704003)
                ·
                  refine ⟨45852681378566593056005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30568454252377728704003 45852681378566593056005)
                  ·
                    refine ⟨8597377758481236198001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45852681378566593056005 8597377758481236198001)
                    ·
                      rfl

theorem cell23_50230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_50230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_50230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_50230 prefixEnd_50230 := by exact prefixLift 50230
  have htrace : WordTrace (prefixWord ++ tailWord_50230) baseStart_50230 baseEnd_50230 := by
    simpa [prefixWord, tailWord_50230, baseEnd_50230] using wordTrace_append hprefix tailTrace_50230
  have hstable : (prefixWord ++ tailWord_50230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50230).length < 2 ^ (prefixWord ++ tailWord_50230).sum := by decide
  have hdescent : baseEnd_50230 < baseStart_50230 := by decide
  rcases family_descends (prefixWord ++ tailWord_50230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50253 : List Nat := [1, 6, 1, 1, 1, 2, 3, 1, 3, 1, 3]
def baseStart_50253 : Nat := 118140960795 + 50253 * 2 ^ 59
def prefixEnd_50253 : Nat := 4983230072969 + 3 ^ 40 * 50253 * 2
def baseEnd_50253 : Nat := 25803943330497118606397

theorem tailTrace_50253 : CollatzResearch.WordTrace tailWord_50253 prefixEnd_50253 25803943330497118606397 := by
  unfold tailWord_50253
  simp only [CollatzResearch.WordTrace]
  refine ⟨1832877486949438374219413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1221918324632958916146275 1832877486949438374219413)
  ·
    refine ⟨85916132200754923791535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1832877486949438374219413 85916132200754923791535)
    ·
      refine ⟨128874198301132385687303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85916132200754923791535 128874198301132385687303)
      ·
        refine ⟨193311297451698578530955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128874198301132385687303 193311297451698578530955)
        ·
          refine ⟨289966946177547867796433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193311297451698578530955 289966946177547867796433)
          ·
            refine ⟨217475209633160900847325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 289966946177547867796433 217475209633160900847325)
            ·
              refine ⟨81553203612435337817747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 217475209633160900847325 81553203612435337817747)
              ·
                refine ⟨122329805418653006726621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81553203612435337817747 122329805418653006726621)
                ·
                  refine ⟨45873677031994877522483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122329805418653006726621 45873677031994877522483)
                  ·
                    refine ⟨68810515547992316283725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45873677031994877522483 68810515547992316283725)
                    ·
                      refine ⟨25803943330497118606397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 68810515547992316283725 25803943330497118606397)
                      ·
                        rfl

theorem cell23_50253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_50253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_50253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_50253 prefixEnd_50253 := by exact prefixLift 50253
  have htrace : WordTrace (prefixWord ++ tailWord_50253) baseStart_50253 baseEnd_50253 := by
    simpa [prefixWord, tailWord_50253, baseEnd_50253] using wordTrace_append hprefix tailTrace_50253
  have hstable : (prefixWord ++ tailWord_50253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50253).length < 2 ^ (prefixWord ++ tailWord_50253).sum := by decide
  have hdescent : baseEnd_50253 < baseStart_50253 := by decide
  rcases family_descends (prefixWord ++ tailWord_50253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50272 : List Nat := [2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 6]
def baseStart_50272 : Nat := 118140960795 + 50272 * 2 ^ 59
def prefixEnd_50272 : Nat := 4983230072969 + 3 ^ 40 * 50272 * 2
def baseEnd_50272 : Nat := 25813699462932544268809

theorem tailTrace_50272 : CollatzResearch.WordTrace tailWord_50272 prefixEnd_50272 25813699462932544268809 := by
  unfold tailWord_50272
  simp only [CollatzResearch.WordTrace]
  refine ⟨916785236940302309580535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1222380315920403079440713 916785236940302309580535)
  ·
    refine ⟨1375177855410453464370803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 916785236940302309580535 1375177855410453464370803)
    ·
      refine ⟨2062766783115680196556205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1375177855410453464370803 2062766783115680196556205)
      ·
        refine ⟨773537543668380073708577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2062766783115680196556205 773537543668380073708577)
        ·
          refine ⟨580153157751285055281433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 773537543668380073708577 580153157751285055281433)
          ·
            refine ⟨435114868313463791461075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 580153157751285055281433 435114868313463791461075)
            ·
              refine ⟨652672302470195687191613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 435114868313463791461075 652672302470195687191613)
              ·
                refine ⟨244752113426323382696855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 652672302470195687191613 244752113426323382696855)
                ·
                  refine ⟨367128170139485074045283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 244752113426323382696855 367128170139485074045283)
                  ·
                    refine ⟨550692255209227611067925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 367128170139485074045283 550692255209227611067925)
                    ·
                      refine ⟨25813699462932544268809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 550692255209227611067925 25813699462932544268809)
                      ·
                        rfl

theorem cell23_50272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_50272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_50272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_50272 prefixEnd_50272 := by exact prefixLift 50272
  have htrace : WordTrace (prefixWord ++ tailWord_50272) baseStart_50272 baseEnd_50272 := by
    simpa [prefixWord, tailWord_50272, baseEnd_50272] using wordTrace_append hprefix tailTrace_50272
  have hstable : (prefixWord ++ tailWord_50272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50272).length < 2 ^ (prefixWord ++ tailWord_50272).sum := by decide
  have hdescent : baseEnd_50272 < baseStart_50272 := by decide
  rcases family_descends (prefixWord ++ tailWord_50272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50276 : List Nat := [2, 3, 1, 1, 2, 1, 1, 3, 5, 2, 2]
def baseStart_50276 : Nat := 118140960795 + 50276 * 2 ^ 59
def prefixEnd_50276 : Nat := 4983230072969 + 3 ^ 40 * 50276 * 2
def baseEnd_50276 : Nat := 25815753385550528618791

theorem tailTrace_50276 : CollatzResearch.WordTrace tailWord_50276 prefixEnd_50276 25815753385550528618791 := by
  unfold tailWord_50276
  simp only [CollatzResearch.WordTrace]
  refine ⟨916858182933056651153341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1222477577244075534871121 916858182933056651153341)
  ·
    refine ⟨343821818599896244182503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 916858182933056651153341 343821818599896244182503)
    ·
      refine ⟨515732727899844366273755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343821818599896244182503 515732727899844366273755)
      ·
        refine ⟨773599091849766549410633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 515732727899844366273755 773599091849766549410633)
        ·
          refine ⟨580199318887324912057975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 773599091849766549410633 580199318887324912057975)
          ·
            refine ⟨870298978330987368086963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 580199318887324912057975 870298978330987368086963)
            ·
              refine ⟨1305448467496481052130445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 870298978330987368086963 1305448467496481052130445)
              ·
                refine ⟨489543175311180394548917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1305448467496481052130445 489543175311180394548917)
                ·
                  refine ⟨45894672685423161988961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 489543175311180394548917 45894672685423161988961)
                  ·
                    refine ⟨34421004514067371491721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45894672685423161988961 34421004514067371491721)
                    ·
                      refine ⟨25815753385550528618791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 34421004514067371491721 25815753385550528618791)
                      ·
                        rfl

theorem cell23_50276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 5, 2, 2].length) (baseStart_50276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_50276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_50276 prefixEnd_50276 := by exact prefixLift 50276
  have htrace : WordTrace (prefixWord ++ tailWord_50276) baseStart_50276 baseEnd_50276 := by
    simpa [prefixWord, tailWord_50276, baseEnd_50276] using wordTrace_append hprefix tailTrace_50276
  have hstable : (prefixWord ++ tailWord_50276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50276).length < 2 ^ (prefixWord ++ tailWord_50276).sum := by decide
  have hdescent : baseEnd_50276 < baseStart_50276 := by decide
  rcases family_descends (prefixWord ++ tailWord_50276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50280 : List Nat := [2, 1, 4, 4, 1, 1, 2, 1, 2, 3, 2]
def baseStart_50280 : Nat := 118140960795 + 50280 * 2 ^ 59
def prefixEnd_50280 : Nat := 4983230072969 + 3 ^ 40 * 50280 * 2
def baseEnd_50280 : Nat := 25817807308168512968773

theorem tailTrace_50280 : CollatzResearch.WordTrace tailWord_50280 prefixEnd_50280 25817807308168512968773 := by
  unfold tailWord_50280
  simp only [CollatzResearch.WordTrace]
  refine ⟨916931128925810992726147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1222574838567747990301529 916931128925810992726147)
  ·
    refine ⟨1375396693388716489089221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 916931128925810992726147 1375396693388716489089221)
    ·
      refine ⟨257886880010384341704229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1375396693388716489089221 257886880010384341704229)
      ·
        refine ⟨48353790001947064069543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 257886880010384341704229 48353790001947064069543)
        ·
          refine ⟨72530685002920596104315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48353790001947064069543 72530685002920596104315)
          ·
            refine ⟨108796027504380894156473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72530685002920596104315 108796027504380894156473)
            ·
              refine ⟨81597020628285670617355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108796027504380894156473 81597020628285670617355)
              ·
                refine ⟨122395530942428505926033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81597020628285670617355 122395530942428505926033)
                ·
                  refine ⟨91796648206821379444525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122395530942428505926033 91796648206821379444525)
                  ·
                    refine ⟨34423743077558017291697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 91796648206821379444525 34423743077558017291697)
                    ·
                      refine ⟨25817807308168512968773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 34423743077558017291697 25817807308168512968773)
                      ·
                        rfl

theorem cell23_50280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_50280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_50280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_50280 prefixEnd_50280 := by exact prefixLift 50280
  have htrace : WordTrace (prefixWord ++ tailWord_50280) baseStart_50280 baseEnd_50280 := by
    simpa [prefixWord, tailWord_50280, baseEnd_50280] using wordTrace_append hprefix tailTrace_50280
  have hstable : (prefixWord ++ tailWord_50280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50280).length < 2 ^ (prefixWord ++ tailWord_50280).sum := by decide
  have hdescent : baseEnd_50280 < baseStart_50280 := by decide
  rcases family_descends (prefixWord ++ tailWord_50280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50336 : List Nat := [2, 1, 1, 4, 2, 1, 1, 3, 3, 3, 2]
def baseStart_50336 : Nat := 118140960795 + 50336 * 2 ^ 59
def prefixEnd_50336 : Nat := 4983230072969 + 3 ^ 40 * 50336 * 2
def baseEnd_50336 : Nat := 25846562224820293868515

theorem tailTrace_50336 : CollatzResearch.WordTrace tailWord_50336 prefixEnd_50336 25846562224820293868515 := by
  unfold tailWord_50336
  simp only [CollatzResearch.WordTrace]
  refine ⟨917952372824371774745431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1223936497099162366327241 917952372824371774745431)
  ·
    refine ⟨1376928559236557662118147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 917952372824371774745431 1376928559236557662118147)
    ·
      refine ⟨2065392838854836493177221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1376928559236557662118147 2065392838854836493177221)
      ·
        refine ⟨387261157285281842470729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2065392838854836493177221 387261157285281842470729)
        ·
          refine ⟨290445867963961381853047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 387261157285281842470729 290445867963961381853047)
          ·
            refine ⟨435668801945942072779571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290445867963961381853047 435668801945942072779571)
            ·
              refine ⟨653503202918913109169357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 435668801945942072779571 653503202918913109169357)
              ·
                refine ⟨245063701094592415938509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 653503202918913109169357 245063701094592415938509)
                ·
                  refine ⟨91898887910472155976941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 245063701094592415938509 91898887910472155976941)
                  ·
                    refine ⟨34462082966427058491353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 91898887910472155976941 34462082966427058491353)
                    ·
                      refine ⟨25846562224820293868515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 34462082966427058491353 25846562224820293868515)
                      ·
                        rfl

theorem cell23_50336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 3, 3, 2].length) (baseStart_50336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_50336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_50336 prefixEnd_50336 := by exact prefixLift 50336
  have htrace : WordTrace (prefixWord ++ tailWord_50336) baseStart_50336 baseEnd_50336 := by
    simpa [prefixWord, tailWord_50336, baseEnd_50336] using wordTrace_append hprefix tailTrace_50336
  have hstable : (prefixWord ++ tailWord_50336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50336).length < 2 ^ (prefixWord ++ tailWord_50336).sum := by decide
  have hdescent : baseEnd_50336 < baseStart_50336 := by decide
  rcases family_descends (prefixWord ++ tailWord_50336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50374 : List Nat := [6, 1, 2, 2, 2, 1, 1, 1, 1, 2, 4]
def baseStart_50374 : Nat := 118140960795 + 50374 * 2 ^ 59
def prefixEnd_50374 : Nat := 4983230072969 + 3 ^ 40 * 50374 * 2
def baseEnd_50374 : Nat := 25866074489691145193341

theorem tailTrace_50374 : CollatzResearch.WordTrace tailWord_50374 prefixEnd_50374 25866074489691145193341 := by
  unfold tailWord_50374
  simp only [CollatzResearch.WordTrace]
  refine ⟨57415334984721126230443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1224860479674050692916117 57415334984721126230443)
  ·
    refine ⟨86123002477081689345665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57415334984721126230443 86123002477081689345665)
    ·
      refine ⟨64592251857811267009249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86123002477081689345665 64592251857811267009249)
      ·
        refine ⟨48444188893358450256937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64592251857811267009249 48444188893358450256937)
        ·
          refine ⟨36333141670018837692703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48444188893358450256937 36333141670018837692703)
          ·
            refine ⟨54499712505028256539055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36333141670018837692703 54499712505028256539055)
            ·
              refine ⟨81749568757542384808583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54499712505028256539055 81749568757542384808583)
              ·
                refine ⟨122624353136313577212875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81749568757542384808583 122624353136313577212875)
                ·
                  refine ⟨183936529704470365819313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122624353136313577212875 183936529704470365819313)
                  ·
                    refine ⟨137952397278352774364485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 183936529704470365819313 137952397278352774364485)
                    ·
                      refine ⟨25866074489691145193341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 137952397278352774364485 25866074489691145193341)
                      ·
                        rfl

theorem cell23_50374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_50374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_50374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_50374 prefixEnd_50374 := by exact prefixLift 50374
  have htrace : WordTrace (prefixWord ++ tailWord_50374) baseStart_50374 baseEnd_50374 := by
    simpa [prefixWord, tailWord_50374, baseEnd_50374] using wordTrace_append hprefix tailTrace_50374
  have hstable : (prefixWord ++ tailWord_50374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50374).length < 2 ^ (prefixWord ++ tailWord_50374).sum := by decide
  have hdescent : baseEnd_50374 < baseStart_50374 := by decide
  rcases family_descends (prefixWord ++ tailWord_50374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50399 : List Nat := [1, 1, 2, 3, 2, 1, 2, 2, 1, 5, 3]
def baseStart_50399 : Nat := 118140960795 + 50399 * 2 ^ 59
def prefixEnd_50399 : Nat := 4983230072969 + 3 ^ 40 * 50399 * 2
def baseEnd_50399 : Nat := 25878911506053547380725

theorem tailTrace_50399 : CollatzResearch.WordTrace tailWord_50399 prefixEnd_50399 25878911506053547380725 := by
  unfold tailWord_50399
  simp only [CollatzResearch.WordTrace]
  refine ⟨1838202544420505309034251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1225468362947003539356167 1838202544420505309034251)
  ·
    refine ⟨2757303816630757963551377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1838202544420505309034251 2757303816630757963551377)
    ·
      refine ⟨2067977862473068472663533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2757303816630757963551377 2067977862473068472663533)
      ·
        refine ⟨775491698427400677248825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2067977862473068472663533 775491698427400677248825)
        ·
          refine ⟨581618773820550507936619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 775491698427400677248825 581618773820550507936619)
          ·
            refine ⟨872428160730825761904929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 581618773820550507936619 872428160730825761904929)
            ·
              refine ⟨654321120548119321428697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 872428160730825761904929 654321120548119321428697)
              ·
                refine ⟨490740840411089491071523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 654321120548119321428697 490740840411089491071523)
                ·
                  refine ⟨736111260616634236607285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 490740840411089491071523 736111260616634236607285)
                  ·
                    refine ⟨69010430682809459681933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 736111260616634236607285 69010430682809459681933)
                    ·
                      refine ⟨25878911506053547380725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 69010430682809459681933 25878911506053547380725)
                      ·
                        rfl

theorem cell23_50399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 5, 3].length) (baseStart_50399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_50399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_50399 prefixEnd_50399 := by exact prefixLift 50399
  have htrace : WordTrace (prefixWord ++ tailWord_50399) baseStart_50399 baseEnd_50399 := by
    simpa [prefixWord, tailWord_50399, baseEnd_50399] using wordTrace_append hprefix tailTrace_50399
  have hstable : (prefixWord ++ tailWord_50399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50399).length < 2 ^ (prefixWord ++ tailWord_50399).sum := by decide
  have hdescent : baseEnd_50399 < baseStart_50399 := by decide
  rcases family_descends (prefixWord ++ tailWord_50399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50419 : List Nat := [1, 1, 1, 2, 2, 5, 1, 1, 4, 5]
def baseStart_50419 : Nat := 118140960795 + 50419 * 2 ^ 59
def prefixEnd_50419 : Nat := 4983230072969 + 3 ^ 40 * 50419 * 2
def baseEnd_50419 : Nat := 8629727039714489710211

theorem tailTrace_50419 : CollatzResearch.WordTrace tailWord_50419 prefixEnd_50419 8629727039714489710211 := by
  unfold tailWord_50419
  simp only [CollatzResearch.WordTrace]
  refine ⟨1838932004348048724762311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1225954669565365816508207 1838932004348048724762311)
  ·
    refine ⟨2758398006522073087143467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1838932004348048724762311 2758398006522073087143467)
    ·
      refine ⟨4137597009783109630715201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2758398006522073087143467 4137597009783109630715201)
      ·
        refine ⟨3103197757337332223036401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4137597009783109630715201 3103197757337332223036401)
        ·
          refine ⟨2327398318002999167277301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3103197757337332223036401 2327398318002999167277301)
          ·
            refine ⟨218193592312781171932247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2327398318002999167277301 218193592312781171932247)
            ·
              refine ⟨327290388469171757898371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218193592312781171932247 327290388469171757898371)
              ·
                refine ⟨490935582703757636847557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 327290388469171757898371 490935582703757636847557)
                ·
                  refine ⟨92050421756954556908917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 490935582703757636847557 92050421756954556908917)
                  ·
                    refine ⟨8629727039714489710211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 92050421756954556908917 8629727039714489710211)
                    ·
                      rfl

theorem cell23_50419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 4, 5].length) (baseStart_50419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_50419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_50419 prefixEnd_50419 := by exact prefixLift 50419
  have htrace : WordTrace (prefixWord ++ tailWord_50419) baseStart_50419 baseEnd_50419 := by
    simpa [prefixWord, tailWord_50419, baseEnd_50419] using wordTrace_append hprefix tailTrace_50419
  have hstable : (prefixWord ++ tailWord_50419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50419).length < 2 ^ (prefixWord ++ tailWord_50419).sum := by decide
  have hdescent : baseEnd_50419 < baseStart_50419 := by decide
  rcases family_descends (prefixWord ++ tailWord_50419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50426 : List Nat := [3, 1, 1, 1, 1, 4, 2, 1, 2, 5, 2]
def baseStart_50426 : Nat := 118140960795 + 50426 * 2 ^ 59
def prefixEnd_50426 : Nat := 4983230072969 + 3 ^ 40 * 50426 * 2
def baseEnd_50426 : Nat := 25892775483724941743101

theorem tailTrace_50426 : CollatzResearch.WordTrace tailWord_50426 prefixEnd_50426 25892775483724941743101 := by
  unfold tailWord_50426
  simp only [CollatzResearch.WordTrace]
  refine ⟨459796828830672230066783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1226124876881792613511421 459796828830672230066783)
  ·
    refine ⟨689695243246008345100175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 459796828830672230066783 689695243246008345100175)
    ·
      refine ⟨1034542864869012517650263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 689695243246008345100175 1034542864869012517650263)
      ·
        refine ⟨1551814297303518776475395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1034542864869012517650263 1551814297303518776475395)
        ·
          refine ⟨2327721445955278164713093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1551814297303518776475395 2327721445955278164713093)
          ·
            refine ⟨436447771116614655883705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2327721445955278164713093 436447771116614655883705)
            ·
              refine ⟨327335828337460991912779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 436447771116614655883705 327335828337460991912779)
              ·
                refine ⟨491003742506191487869169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 327335828337460991912779 491003742506191487869169)
                ·
                  refine ⟨368252806879643615901877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 491003742506191487869169 368252806879643615901877)
                  ·
                    refine ⟨34523700644966588990801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 368252806879643615901877 34523700644966588990801)
                    ·
                      refine ⟨25892775483724941743101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 34523700644966588990801 25892775483724941743101)
                      ·
                        rfl

theorem cell23_50426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 2, 5, 2].length) (baseStart_50426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_50426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_50426 prefixEnd_50426 := by exact prefixLift 50426
  have htrace : WordTrace (prefixWord ++ tailWord_50426) baseStart_50426 baseEnd_50426 := by
    simpa [prefixWord, tailWord_50426, baseEnd_50426] using wordTrace_append hprefix tailTrace_50426
  have hstable : (prefixWord ++ tailWord_50426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50426).length < 2 ^ (prefixWord ++ tailWord_50426).sum := by decide
  have hdescent : baseEnd_50426 < baseStart_50426 := by decide
  rcases family_descends (prefixWord ++ tailWord_50426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50456 : List Nat := [2, 1, 2, 3, 1, 3, 1, 3, 2, 1, 4]
def baseStart_50456 : Nat := 118140960795 + 50456 * 2 ^ 59
def prefixEnd_50456 : Nat := 4983230072969 + 3 ^ 40 * 50456 * 2
def baseEnd_50456 : Nat := 25908179903359824367963

theorem tailTrace_50456 : CollatzResearch.WordTrace tailWord_50456 prefixEnd_50456 25908179903359824367963 := by
  unfold tailWord_50456
  simp only [CollatzResearch.WordTrace]
  refine ⟨920140752607002021929611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1226854336809336029239481 920140752607002021929611)
  ·
    refine ⟨1380211128910503032894417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 920140752607002021929611 1380211128910503032894417)
    ·
      refine ⟨1035158346682877274670813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1380211128910503032894417 1035158346682877274670813)
      ·
        refine ⟨388184380006078978001555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1035158346682877274670813 388184380006078978001555)
        ·
          refine ⟨582276570009118467002333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 388184380006078978001555 582276570009118467002333)
          ·
            refine ⟨218353713753419425125875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 582276570009118467002333 218353713753419425125875)
            ·
              refine ⟨327530570630129137688813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218353713753419425125875 327530570630129137688813)
              ·
                refine ⟨122823963986298426633305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 327530570630129137688813 122823963986298426633305)
                ·
                  refine ⟨92117972989723819974979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122823963986298426633305 92117972989723819974979)
                  ·
                    refine ⟨138176959484585729962469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 92117972989723819974979 138176959484585729962469)
                    ·
                      refine ⟨25908179903359824367963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 138176959484585729962469 25908179903359824367963)
                      ·
                        rfl

theorem cell23_50456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_50456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_50456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_50456 prefixEnd_50456 := by exact prefixLift 50456
  have htrace : WordTrace (prefixWord ++ tailWord_50456) baseStart_50456 baseEnd_50456 := by
    simpa [prefixWord, tailWord_50456, baseEnd_50456] using wordTrace_append hprefix tailTrace_50456
  have hstable : (prefixWord ++ tailWord_50456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50456).length < 2 ^ (prefixWord ++ tailWord_50456).sum := by decide
  have hdescent : baseEnd_50456 < baseStart_50456 := by decide
  rcases family_descends (prefixWord ++ tailWord_50456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50500 : List Nat := [2, 3, 4, 1, 1, 2, 1, 2, 3, 4]
def baseStart_50500 : Nat := 118140960795 + 50500 * 2 ^ 59
def prefixEnd_50500 : Nat := 4983230072969 + 3 ^ 40 * 50500 * 2
def baseEnd_50500 : Nat := 8643591017385884072587

theorem tailTrace_50500 : CollatzResearch.WordTrace tailWord_50500 prefixEnd_50500 8643591017385884072587 := by
  unfold tailWord_50500
  simp only [CollatzResearch.WordTrace]
  refine ⟨920943158527299779230477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1227924211369733038973969 920943158527299779230477)
  ·
    refine ⟨345353684447737417211429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 920943158527299779230477 345353684447737417211429)
    ·
      refine ⟨64753815833950765727143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 345353684447737417211429 64753815833950765727143)
      ·
        refine ⟨97130723750926148590715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64753815833950765727143 97130723750926148590715)
        ·
          refine ⟨145696085626389222886073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97130723750926148590715 145696085626389222886073)
          ·
            refine ⟨109272064219791917164555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145696085626389222886073 109272064219791917164555)
            ·
              refine ⟨163908096329687875746833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109272064219791917164555 163908096329687875746833)
              ·
                refine ⟨122931072247265906810125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 163908096329687875746833 122931072247265906810125)
                ·
                  refine ⟨46099152092724715053797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122931072247265906810125 46099152092724715053797)
                  ·
                    refine ⟨8643591017385884072587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46099152092724715053797 8643591017385884072587)
                    ·
                      rfl

theorem cell23_50500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_50500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_50500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_50500 prefixEnd_50500 := by exact prefixLift 50500
  have htrace : WordTrace (prefixWord ++ tailWord_50500) baseStart_50500 baseEnd_50500 := by
    simpa [prefixWord, tailWord_50500, baseEnd_50500] using wordTrace_append hprefix tailTrace_50500
  have hstable : (prefixWord ++ tailWord_50500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50500).length < 2 ^ (prefixWord ++ tailWord_50500).sum := by decide
  have hdescent : baseEnd_50500 < baseStart_50500 := by decide
  rcases family_descends (prefixWord ++ tailWord_50500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50533 : List Nat := [1, 3, 1, 3, 1, 2, 2, 1, 4, 3, 2]
def baseStart_50533 : Nat := 118140960795 + 50533 * 2 ^ 59
def prefixEnd_50533 : Nat := 4983230072969 + 3 ^ 40 * 50533 * 2
def baseEnd_50533 : Nat := 25947717913756023105109

theorem tailTrace_50533 : CollatzResearch.WordTrace tailWord_50533 prefixEnd_50533 25947717913756023105109 := by
  unfold tailWord_50533
  simp only [CollatzResearch.WordTrace]
  refine ⟨1843089925935046194412253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1228726617290030796274835 1843089925935046194412253)
  ·
    refine ⟨691158722225642322904595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1843089925935046194412253 691158722225642322904595)
    ·
      refine ⟨1036738083338463484356893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 691158722225642322904595 1036738083338463484356893)
      ·
        refine ⟨388776781251923806633835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1036738083338463484356893 388776781251923806633835)
        ·
          refine ⟨583165171877885709950753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 388776781251923806633835 583165171877885709950753)
          ·
            refine ⟨437373878908414282463065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 583165171877885709950753 437373878908414282463065)
            ·
              refine ⟨328030409181310711847299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 437373878908414282463065 328030409181310711847299)
              ·
                refine ⟨492045613771966067770949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 328030409181310711847299 492045613771966067770949)
                ·
                  refine ⟨92258552582243637707053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 492045613771966067770949 92258552582243637707053)
                  ·
                    refine ⟨34596957218341364140145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 92258552582243637707053 34596957218341364140145)
                    ·
                      refine ⟨25947717913756023105109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 34596957218341364140145 25947717913756023105109)
                      ·
                        rfl

theorem cell23_50533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 4, 3, 2].length) (baseStart_50533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_50533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_50533 prefixEnd_50533 := by exact prefixLift 50533
  have htrace : WordTrace (prefixWord ++ tailWord_50533) baseStart_50533 baseEnd_50533 := by
    simpa [prefixWord, tailWord_50533, baseEnd_50533] using wordTrace_append hprefix tailTrace_50533
  have hstable : (prefixWord ++ tailWord_50533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50533).length < 2 ^ (prefixWord ++ tailWord_50533).sum := by decide
  have hdescent : baseEnd_50533 < baseStart_50533 := by decide
  rcases family_descends (prefixWord ++ tailWord_50533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50540 : List Nat := [2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 3]
def baseStart_50540 : Nat := 118140960795 + 50540 * 2 ^ 59
def prefixEnd_50540 : Nat := 4983230072969 + 3 ^ 40 * 50540 * 2
def baseEnd_50540 : Nat := 25951312278337495717577

theorem tailTrace_50540 : CollatzResearch.WordTrace tailWord_50540 prefixEnd_50540 25951312278337495717577 := by
  unfold tailWord_50540
  simp only [CollatzResearch.WordTrace]
  refine ⟨921672618454843194958537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1228896824606457593278049 921672618454843194958537)
  ·
    refine ⟨691254463841132396218903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 921672618454843194958537 691254463841132396218903)
    ·
      refine ⟨1036881695761698594328355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 691254463841132396218903 1036881695761698594328355)
      ·
        refine ⟨1555322543642547891492533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1036881695761698594328355 1555322543642547891492533)
        ·
          refine ⟨145811488466488864827425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1555322543642547891492533 145811488466488864827425)
          ·
            refine ⟨109358616349866648620569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145811488466488864827425 109358616349866648620569)
            ·
              refine ⟨82018962262399986465427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109358616349866648620569 82018962262399986465427)
              ·
                refine ⟨123028443393599979698141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82018962262399986465427 123028443393599979698141)
                ·
                  refine ⟨46135666272599992386803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123028443393599979698141 46135666272599992386803)
                  ·
                    refine ⟨69203499408899988580205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46135666272599992386803 69203499408899988580205)
                    ·
                      refine ⟨25951312278337495717577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 69203499408899988580205 25951312278337495717577)
                      ·
                        rfl

theorem cell23_50540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 3].length) (baseStart_50540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_50540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_50540 prefixEnd_50540 := by exact prefixLift 50540
  have htrace : WordTrace (prefixWord ++ tailWord_50540) baseStart_50540 baseEnd_50540 := by
    simpa [prefixWord, tailWord_50540, baseEnd_50540] using wordTrace_append hprefix tailTrace_50540
  have hstable : (prefixWord ++ tailWord_50540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50540).length < 2 ^ (prefixWord ++ tailWord_50540).sum := by decide
  have hdescent : baseEnd_50540 < baseStart_50540 := by decide
  rcases family_descends (prefixWord ++ tailWord_50540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50563 : List Nat := [1, 1, 1, 3, 5, 1, 1, 4, 1, 1, 4]
def baseStart_50563 : Nat := 118140960795 + 50563 * 2 ^ 59
def prefixEnd_50563 : Nat := 4983230072969 + 3 ^ 40 * 50563 * 2
def baseEnd_50563 : Nat := 25963122333390905729971

theorem tailTrace_50563 : CollatzResearch.WordTrace tailWord_50563 prefixEnd_50563 25963122333390905729971 := by
  unfold tailWord_50563
  simp only [CollatzResearch.WordTrace]
  refine ⟨1844184115826361318004343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1229456077217574212002895 1844184115826361318004343)
  ·
    refine ⟨2766276173739541977006515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1844184115826361318004343 2766276173739541977006515)
    ·
      refine ⟨4149414260609312965509773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2766276173739541977006515 4149414260609312965509773)
      ·
        refine ⟨1556030347728492362066165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4149414260609312965509773 1556030347728492362066165)
        ·
          refine ⟨145877845099546158943703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1556030347728492362066165 145877845099546158943703)
          ·
            refine ⟨218816767649319238415555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145877845099546158943703 218816767649319238415555)
            ·
              refine ⟨328225151473978857623333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218816767649319238415555 328225151473978857623333)
              ·
                refine ⟨61542215901371035804375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 328225151473978857623333 61542215901371035804375)
                ·
                  refine ⟨92313323852056553706563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61542215901371035804375 92313323852056553706563)
                  ·
                    refine ⟨138469985778084830559845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 92313323852056553706563 138469985778084830559845)
                    ·
                      refine ⟨25963122333390905729971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 138469985778084830559845 25963122333390905729971)
                      ·
                        rfl

theorem cell23_50563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 4, 1, 1, 4].length) (baseStart_50563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_50563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_50563 prefixEnd_50563 := by exact prefixLift 50563
  have htrace : WordTrace (prefixWord ++ tailWord_50563) baseStart_50563 baseEnd_50563 := by
    simpa [prefixWord, tailWord_50563, baseEnd_50563] using wordTrace_append hprefix tailTrace_50563
  have hstable : (prefixWord ++ tailWord_50563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50563).length < 2 ^ (prefixWord ++ tailWord_50563).sum := by decide
  have hdescent : baseEnd_50563 < baseStart_50563 := by decide
  rcases family_descends (prefixWord ++ tailWord_50563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50580 : List Nat := [2, 4, 2, 1, 2, 1, 2, 3, 1, 1, 4]
def baseStart_50580 : Nat := 118140960795 + 50580 * 2 ^ 59
def prefixEnd_50580 : Nat := 4983230072969 + 3 ^ 40 * 50580 * 2
def baseEnd_50580 : Nat := 25971851504517339217393

theorem tailTrace_50580 : CollatzResearch.WordTrace tailWord_50580 prefixEnd_50580 25971851504517339217393 := by
  unfold tailWord_50580
  simp only [CollatzResearch.WordTrace]
  refine ⟨922402078382386610686597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1229869437843182147582129 922402078382386610686597)
  ·
    refine ⟨172950389696697489503737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 922402078382386610686597 172950389696697489503737)
    ·
      refine ⟨129712792272523117127803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172950389696697489503737 129712792272523117127803)
      ·
        refine ⟨194569188408784675691705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129712792272523117127803 194569188408784675691705)
        ·
          refine ⟨145926891306588506768779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194569188408784675691705 145926891306588506768779)
          ·
            refine ⟨218890336959882760153169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145926891306588506768779 218890336959882760153169)
            ·
              refine ⟨164167752719912070114877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 218890336959882760153169 164167752719912070114877)
              ·
                refine ⟨61562907269967026293079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 164167752719912070114877 61562907269967026293079)
                ·
                  refine ⟨92344360904950539439619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61562907269967026293079 92344360904950539439619)
                  ·
                    refine ⟨138516541357425809159429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 92344360904950539439619 138516541357425809159429)
                    ·
                      refine ⟨25971851504517339217393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 138516541357425809159429 25971851504517339217393)
                      ·
                        rfl

theorem cell23_50580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_50580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_50580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_50580 prefixEnd_50580 := by exact prefixLift 50580
  have htrace : WordTrace (prefixWord ++ tailWord_50580) baseStart_50580 baseEnd_50580 := by
    simpa [prefixWord, tailWord_50580, baseEnd_50580] using wordTrace_append hprefix tailTrace_50580
  have hstable : (prefixWord ++ tailWord_50580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50580).length < 2 ^ (prefixWord ++ tailWord_50580).sum := by decide
  have hdescent : baseEnd_50580 < baseStart_50580 := by decide
  rcases family_descends (prefixWord ++ tailWord_50580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50617 : List Nat := [1, 2, 1, 4, 4, 2, 1, 2, 1, 2, 3]
def baseStart_50617 : Nat := 118140960795 + 50617 * 2 ^ 59
def prefixEnd_50617 : Nat := 4983230072969 + 3 ^ 40 * 50617 * 2
def baseEnd_50617 : Nat := 25990850288733694454723

theorem tailTrace_50617 : CollatzResearch.WordTrace tailWord_50617 prefixEnd_50617 25990850288733694454723 := by
  unfold tailWord_50617
  simp only [CollatzResearch.WordTrace]
  refine ⟨1846153657630728540470105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1230769105087152360313403 1846153657630728540470105)
  ·
    refine ⟨1384615243223046405352579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1846153657630728540470105 1384615243223046405352579)
    ·
      refine ⟨2076922864834569608028869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1384615243223046405352579 2076922864834569608028869)
      ·
        refine ⟨389423037156481801505413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2076922864834569608028869 389423037156481801505413)
        ·
          refine ⟨73016819466840337782265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 389423037156481801505413 73016819466840337782265)
          ·
            refine ⟨54762614600130253336699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73016819466840337782265 54762614600130253336699)
            ·
              refine ⟨82143921900195380005049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54762614600130253336699 82143921900195380005049)
              ·
                refine ⟨61607941425146535003787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82143921900195380005049 61607941425146535003787)
                ·
                  refine ⟨92411912137719802505681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61607941425146535003787 92411912137719802505681)
                  ·
                    refine ⟨69308934103289851879261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 92411912137719802505681 69308934103289851879261)
                    ·
                      refine ⟨25990850288733694454723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 69308934103289851879261 25990850288733694454723)
                      ·
                        rfl

theorem cell23_50617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 2, 1, 2, 3].length) (baseStart_50617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_50617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_50617 prefixEnd_50617 := by exact prefixLift 50617
  have htrace : WordTrace (prefixWord ++ tailWord_50617) baseStart_50617 baseEnd_50617 := by
    simpa [prefixWord, tailWord_50617, baseEnd_50617] using wordTrace_append hprefix tailTrace_50617
  have hstable : (prefixWord ++ tailWord_50617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50617).length < 2 ^ (prefixWord ++ tailWord_50617).sum := by decide
  have hdescent : baseEnd_50617 < baseStart_50617 := by decide
  rcases family_descends (prefixWord ++ tailWord_50617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50653 : List Nat := [1, 4, 3, 1, 1, 2, 1, 1, 2, 3, 4]
def baseStart_50653 : Nat := 118140960795 + 50653 * 2 ^ 59
def prefixEnd_50653 : Nat := 4983230072969 + 3 ^ 40 * 50653 * 2
def baseEnd_50653 : Nat := 26009335592295553604557

theorem tailTrace_50653 : CollatzResearch.WordTrace tailWord_50653 prefixEnd_50653 26009335592295553604557 := by
  unfold tailWord_50653
  simp only [CollatzResearch.WordTrace]
  refine ⟨1847466685500306688780613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1231644457000204459187075 1847466685500306688780613)
  ·
    refine ⟨346400003531307504146365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1847466685500306688780613 346400003531307504146365)
    ·
      refine ⟨129900001324240314054887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 346400003531307504146365 129900001324240314054887)
      ·
        refine ⟨194850001986360471082331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129900001324240314054887 194850001986360471082331)
        ·
          refine ⟨292275002979540706623497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194850001986360471082331 292275002979540706623497)
          ·
            refine ⟨219206252234655529967623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 292275002979540706623497 219206252234655529967623)
            ·
              refine ⟨328809378351983294951435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219206252234655529967623 328809378351983294951435)
              ·
                refine ⟨493214067527974942427153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 328809378351983294951435 493214067527974942427153)
                ·
                  refine ⟨369910550645981206820365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 493214067527974942427153 369910550645981206820365)
                  ·
                    refine ⟨138716456492242952557637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 369910550645981206820365 138716456492242952557637)
                    ·
                      refine ⟨26009335592295553604557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 138716456492242952557637 26009335592295553604557)
                      ·
                        rfl

theorem cell23_50653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_50653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_50653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_50653 prefixEnd_50653 := by exact prefixLift 50653
  have htrace : WordTrace (prefixWord ++ tailWord_50653) baseStart_50653 baseEnd_50653 := by
    simpa [prefixWord, tailWord_50653, baseEnd_50653] using wordTrace_append hprefix tailTrace_50653
  have hstable : (prefixWord ++ tailWord_50653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50653).length < 2 ^ (prefixWord ++ tailWord_50653).sum := by decide
  have hdescent : baseEnd_50653 < baseStart_50653 := by decide
  rcases family_descends (prefixWord ++ tailWord_50653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50656 : List Nat := [2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 5]
def baseStart_50656 : Nat := 118140960795 + 50656 * 2 ^ 59
def prefixEnd_50656 : Nat := 4983230072969 + 3 ^ 40 * 50656 * 2
def baseEnd_50656 : Nat := 26010876034259041867043

theorem tailTrace_50656 : CollatzResearch.WordTrace tailWord_50656 prefixEnd_50656 26010876034259041867043 := by
  unfold tailWord_50656
  simp only [CollatzResearch.WordTrace]
  refine ⟨923788052244719100569911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1231717402992958800759881 923788052244719100569911)
  ·
    refine ⟨1385682078367078650854867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 923788052244719100569911 1385682078367078650854867)
    ·
      refine ⟨2078523117550617976282301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1385682078367078650854867 2078523117550617976282301)
      ·
        refine ⟨779446169081481741105863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2078523117550617976282301 779446169081481741105863)
        ·
          refine ⟨1169169253622222611658795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 779446169081481741105863 1169169253622222611658795)
          ·
            refine ⟨1753753880433333917488193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1169169253622222611658795 1753753880433333917488193)
            ·
              refine ⟨1315315410325000438116145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1753753880433333917488193 1315315410325000438116145)
              ·
                refine ⟨986486557743750328587109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1315315410325000438116145 986486557743750328587109)
                ·
                  refine ⟨184966229576953186610083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 986486557743750328587109 184966229576953186610083)
                  ·
                    refine ⟨277449344365429779915125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 184966229576953186610083 277449344365429779915125)
                    ·
                      refine ⟨26010876034259041867043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 277449344365429779915125 26010876034259041867043)
                      ·
                        rfl

theorem cell23_50656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_50656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_50656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_50656 prefixEnd_50656 := by exact prefixLift 50656
  have htrace : WordTrace (prefixWord ++ tailWord_50656) baseStart_50656 baseEnd_50656 := by
    simpa [prefixWord, tailWord_50656, baseEnd_50656] using wordTrace_append hprefix tailTrace_50656
  have hstable : (prefixWord ++ tailWord_50656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50656).length < 2 ^ (prefixWord ++ tailWord_50656).sum := by decide
  have hdescent : baseEnd_50656 < baseStart_50656 := by decide
  rcases family_descends (prefixWord ++ tailWord_50656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50663 : List Nat := [1, 1, 5, 2, 1, 3, 1, 1, 2, 6]
def baseStart_50663 : Nat := 118140960795 + 50663 * 2 ^ 59
def prefixEnd_50663 : Nat := 4983230072969 + 3 ^ 40 * 50663 * 2
def baseEnd_50663 : Nat := 8671490132946838159837

theorem tailTrace_50663 : CollatzResearch.WordTrace tailWord_50663 prefixEnd_50663 8671490132946838159837 := by
  unfold tailWord_50663
  simp only [CollatzResearch.WordTrace]
  refine ⟨1847831415464078396644643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1231887610309385597763095 1847831415464078396644643)
  ·
    refine ⟨2771747123196117594966965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1847831415464078396644643 2771747123196117594966965)
    ·
      refine ⟨259851292799636024528153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2771747123196117594966965 259851292799636024528153)
      ·
        refine ⟨194888469599727018396115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259851292799636024528153 194888469599727018396115)
        ·
          refine ⟨292332704399590527594173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194888469599727018396115 292332704399590527594173)
          ·
            refine ⟨109624764149846447847815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 292332704399590527594173 109624764149846447847815)
            ·
              refine ⟨164437146224769671771723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109624764149846447847815 164437146224769671771723)
              ·
                refine ⟨246655719337154507657585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164437146224769671771723 246655719337154507657585)
                ·
                  refine ⟨184991789502865880743189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 246655719337154507657585 184991789502865880743189)
                  ·
                    refine ⟨8671490132946838159837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 184991789502865880743189 8671490132946838159837)
                    ·
                      rfl

theorem cell23_50663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_50663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_50663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_50663 prefixEnd_50663 := by exact prefixLift 50663
  have htrace : WordTrace (prefixWord ++ tailWord_50663) baseStart_50663 baseEnd_50663 := by
    simpa [prefixWord, tailWord_50663, baseEnd_50663] using wordTrace_append hprefix tailTrace_50663
  have hstable : (prefixWord ++ tailWord_50663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50663).length < 2 ^ (prefixWord ++ tailWord_50663).sum := by decide
  have hdescent : baseEnd_50663 < baseStart_50663 := by decide
  rcases family_descends (prefixWord ++ tailWord_50663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50720 : List Nat := [2, 1, 1, 6, 1, 1, 2, 1, 2, 3, 3]
def baseStart_50720 : Nat := 118140960795 + 50720 * 2 ^ 59
def prefixEnd_50720 : Nat := 4983230072969 + 3 ^ 40 * 50720 * 2
def baseEnd_50720 : Nat := 26043738796146791466749

theorem tailTrace_50720 : CollatzResearch.WordTrace tailWord_50720 prefixEnd_50720 26043738796146791466749 := by
  unfold tailWord_50720
  simp only [CollatzResearch.WordTrace]
  refine ⟨924955188128788565734807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1233273584171718087646409 924955188128788565734807)
  ·
    refine ⟨1387432782193182848602211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 924955188128788565734807 1387432782193182848602211)
    ·
      refine ⟨2081149173289774272903317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1387432782193182848602211 2081149173289774272903317)
      ·
        refine ⟨97553867497958169042343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 2081149173289774272903317 97553867497958169042343)
        ·
          refine ⟨146330801246937253563515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97553867497958169042343 146330801246937253563515)
          ·
            refine ⟨219496201870405880345273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146330801246937253563515 219496201870405880345273)
            ·
              refine ⟨164622151402804410258955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 219496201870405880345273 164622151402804410258955)
              ·
                refine ⟨246933227104206615388433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164622151402804410258955 246933227104206615388433)
                ·
                  refine ⟨185199920328154961541325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 246933227104206615388433 185199920328154961541325)
                  ·
                    refine ⟨69449970123058110577997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 185199920328154961541325 69449970123058110577997)
                    ·
                      refine ⟨26043738796146791466749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 69449970123058110577997 26043738796146791466749)
                      ·
                        rfl

theorem cell23_50720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_50720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_50720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_50720 prefixEnd_50720 := by exact prefixLift 50720
  have htrace : WordTrace (prefixWord ++ tailWord_50720) baseStart_50720 baseEnd_50720 := by
    simpa [prefixWord, tailWord_50720, baseEnd_50720] using wordTrace_append hprefix tailTrace_50720
  have hstable : (prefixWord ++ tailWord_50720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50720).length < 2 ^ (prefixWord ++ tailWord_50720).sum := by decide
  have hdescent : baseEnd_50720 < baseStart_50720 := by decide
  rcases family_descends (prefixWord ++ tailWord_50720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50736 : List Nat := [2, 1, 1, 1, 2, 3, 1, 1, 1, 10]
def baseStart_50736 : Nat := 118140960795 + 50736 * 2 ^ 59
def prefixEnd_50736 : Nat := 4983230072969 + 3 ^ 40 * 50736 * 2
def baseEnd_50736 : Nat := 8683984828872909622225

theorem tailTrace_50736 : CollatzResearch.WordTrace tailWord_50736 prefixEnd_50736 8683984828872909622225 := by
  unfold tailWord_50736
  simp only [CollatzResearch.WordTrace]
  refine ⟨925246972099805932026031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1233662629466407909368041 925246972099805932026031)
  ·
    refine ⟨1387870458149708898039047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 925246972099805932026031 1387870458149708898039047)
    ·
      refine ⟨2081805687224563347058571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1387870458149708898039047 2081805687224563347058571)
      ·
        refine ⟨3122708530836845020587857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2081805687224563347058571 3122708530836845020587857)
        ·
          refine ⟨2342031398127633765440893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3122708530836845020587857 2342031398127633765440893)
          ·
            refine ⟨878261774297862662040335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2342031398127633765440893 878261774297862662040335)
            ·
              refine ⟨1317392661446793993060503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 878261774297862662040335 1317392661446793993060503)
              ·
                refine ⟨1976088992170190989590755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1317392661446793993060503 1976088992170190989590755)
                ·
                  refine ⟨2964133488255286484386133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1976088992170190989590755 2964133488255286484386133)
                  ·
                    refine ⟨8683984828872909622225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 2964133488255286484386133 8683984828872909622225)
                    ·
                      rfl

theorem cell23_50736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 1, 10].length) (baseStart_50736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_50736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_50736 prefixEnd_50736 := by exact prefixLift 50736
  have htrace : WordTrace (prefixWord ++ tailWord_50736) baseStart_50736 baseEnd_50736 := by
    simpa [prefixWord, tailWord_50736, baseEnd_50736] using wordTrace_append hprefix tailTrace_50736
  have hstable : (prefixWord ++ tailWord_50736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50736).length < 2 ^ (prefixWord ++ tailWord_50736).sum := by decide
  have hdescent : baseEnd_50736 < baseStart_50736 := by decide
  rcases family_descends (prefixWord ++ tailWord_50736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50743 : List Nat := [1, 1, 3, 1, 2, 4, 2, 1, 1, 3, 4]
def baseStart_50743 : Nat := 118140960795 + 50743 * 2 ^ 59
def prefixEnd_50743 : Nat := 4983230072969 + 3 ^ 40 * 50743 * 2
def baseEnd_50743 : Nat := 26055548851200201479143

theorem tailTrace_50743 : CollatzResearch.WordTrace tailWord_50743 prefixEnd_50743 26055548851200201479143 := by
  unfold tailWord_50743
  simp only [CollatzResearch.WordTrace]
  refine ⟨1850749255174252059556883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1233832836782834706371255 1850749255174252059556883)
  ·
    refine ⟨2776123882761378089335325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1850749255174252059556883 2776123882761378089335325)
    ·
      refine ⟨1041046456035516783500747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2776123882761378089335325 1041046456035516783500747)
      ·
        refine ⟨1561569684053275175251121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1041046456035516783500747 1561569684053275175251121)
        ·
          refine ⟨1171177263039956381438341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1561569684053275175251121 1171177263039956381438341)
          ·
            refine ⟨219595736819991821519689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1171177263039956381438341 219595736819991821519689)
            ·
              refine ⟨164696802614993866139767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 219595736819991821519689 164696802614993866139767)
              ·
                refine ⟨247045203922490799209651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164696802614993866139767 247045203922490799209651)
                ·
                  refine ⟨370567805883736198814477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 247045203922490799209651 370567805883736198814477)
                  ·
                    refine ⟨138962927206401074555429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 370567805883736198814477 138962927206401074555429)
                    ·
                      refine ⟨26055548851200201479143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 138962927206401074555429 26055548851200201479143)
                      ·
                        rfl

theorem cell23_50743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 3, 4].length) (baseStart_50743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_50743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_50743 prefixEnd_50743 := by exact prefixLift 50743
  have htrace : WordTrace (prefixWord ++ tailWord_50743) baseStart_50743 baseEnd_50743 := by
    simpa [prefixWord, tailWord_50743, baseEnd_50743] using wordTrace_append hprefix tailTrace_50743
  have hstable : (prefixWord ++ tailWord_50743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50743).length < 2 ^ (prefixWord ++ tailWord_50743).sum := by decide
  have hdescent : baseEnd_50743 < baseStart_50743 := by decide
  rcases family_descends (prefixWord ++ tailWord_50743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50793 : List Nat := [1, 2, 1, 1, 1, 4, 2, 1, 2, 5, 3]
def baseStart_50793 : Nat := 118140960795 + 50793 * 2 ^ 59
def prefixEnd_50793 : Nat := 4983230072969 + 3 ^ 40 * 50793 * 2
def baseEnd_50793 : Nat := 26081222883925005853913

theorem tailTrace_50793 : CollatzResearch.WordTrace tailWord_50793 prefixEnd_50793 26081222883925005853913 := by
  unfold tailWord_50793
  simp only [CollatzResearch.WordTrace]
  refine ⟨1852572904993110598877033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1235048603328740399251355 1852572904993110598877033)
  ·
    refine ⟨1389429678744832949157775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1852572904993110598877033 1389429678744832949157775)
    ·
      refine ⟨2084144518117249423736663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1389429678744832949157775 2084144518117249423736663)
      ·
        refine ⟨3126216777175874135604995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2084144518117249423736663 3126216777175874135604995)
        ·
          refine ⟨4689325165763811203407493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3126216777175874135604995 4689325165763811203407493)
          ·
            refine ⟨879248468580714600638905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4689325165763811203407493 879248468580714600638905)
            ·
              refine ⟨659436351435535950479179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 879248468580714600638905 659436351435535950479179)
              ·
                refine ⟨989154527153303925718769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 659436351435535950479179 989154527153303925718769)
                ·
                  refine ⟨741865895364977944289077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 989154527153303925718769 741865895364977944289077)
                  ·
                    refine ⟨69549927690466682277101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 741865895364977944289077 69549927690466682277101)
                    ·
                      refine ⟨26081222883925005853913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 69549927690466682277101 26081222883925005853913)
                      ·
                        rfl

theorem cell23_50793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 5, 3].length) (baseStart_50793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_50793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_50793 prefixEnd_50793 := by exact prefixLift 50793
  have htrace : WordTrace (prefixWord ++ tailWord_50793) baseStart_50793 baseEnd_50793 := by
    simpa [prefixWord, tailWord_50793, baseEnd_50793] using wordTrace_append hprefix tailTrace_50793
  have hstable : (prefixWord ++ tailWord_50793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50793).length < 2 ^ (prefixWord ++ tailWord_50793).sum := by decide
  have hdescent : baseEnd_50793 < baseStart_50793 := by decide
  rcases family_descends (prefixWord ++ tailWord_50793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50810 : List Nat := [3, 1, 1, 1, 1, 1, 1, 3, 7, 1, 3]
def baseStart_50810 : Nat := 118140960795 + 50810 * 2 ^ 59
def prefixEnd_50810 : Nat := 4983230072969 + 3 ^ 40 * 50810 * 2
def baseEnd_50810 : Nat := 26089952055051439341335

theorem tailTrace_50810 : CollatzResearch.WordTrace tailWord_50810 prefixEnd_50810 26089952055051439341335 := by
  unfold tailWord_50810
  simp only [CollatzResearch.WordTrace]
  refine ⟨463298236482880625561471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1235461963954348334830589 463298236482880625561471)
  ·
    refine ⟨694947354724320938342207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 463298236482880625561471 694947354724320938342207)
    ·
      refine ⟨1042421032086481407513311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 694947354724320938342207 1042421032086481407513311)
      ·
        refine ⟨1563631548129722111269967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1042421032086481407513311 1563631548129722111269967)
        ·
          refine ⟨2345447322194583166904951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1563631548129722111269967 2345447322194583166904951)
          ·
            refine ⟨3518170983291874750357427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2345447322194583166904951 3518170983291874750357427)
            ·
              refine ⟨5277256474937812125536141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3518170983291874750357427 5277256474937812125536141)
              ·
                refine ⟨1978971178101679547076053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5277256474937812125536141 1978971178101679547076053)
                ·
                  refine ⟨46382136986758114384595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1978971178101679547076053 46382136986758114384595)
                  ·
                    refine ⟨69573205480137171576893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46382136986758114384595 69573205480137171576893)
                    ·
                      refine ⟨26089952055051439341335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 69573205480137171576893 26089952055051439341335)
                      ·
                        rfl

theorem cell23_50810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 7, 1, 3].length) (baseStart_50810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_50810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_50810 prefixEnd_50810 := by exact prefixLift 50810
  have htrace : WordTrace (prefixWord ++ tailWord_50810) baseStart_50810 baseEnd_50810 := by
    simpa [prefixWord, tailWord_50810, baseEnd_50810] using wordTrace_append hprefix tailTrace_50810
  have hstable : (prefixWord ++ tailWord_50810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50810).length < 2 ^ (prefixWord ++ tailWord_50810).sum := by decide
  have hdescent : baseEnd_50810 < baseStart_50810 := by decide
  rcases family_descends (prefixWord ++ tailWord_50810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50830 : List Nat := [4, 1, 1, 3, 1, 2, 1, 2, 3, 5]
def baseStart_50830 : Nat := 118140960795 + 50830 * 2 ^ 59
def prefixEnd_50830 : Nat := 4983230072969 + 3 ^ 40 * 50830 * 2
def baseEnd_50830 : Nat := 8700073889380453697081

theorem tailTrace_50830 : CollatzResearch.WordTrace tailWord_50830 prefixEnd_50830 8700073889380453697081 := by
  unfold tailWord_50830
  simp only [CollatzResearch.WordTrace]
  refine ⟨231740300732383239746743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1235948270572710611982629 231740300732383239746743)
  ·
    refine ⟨347610451098574859620115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231740300732383239746743 347610451098574859620115)
    ·
      refine ⟨521415676647862289430173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347610451098574859620115 521415676647862289430173)
      ·
        refine ⟨195530878742948358536315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 521415676647862289430173 195530878742948358536315)
        ·
          refine ⟨293296318114422537804473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195530878742948358536315 293296318114422537804473)
          ·
            refine ⟨219972238585816903353355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 293296318114422537804473 219972238585816903353355)
            ·
              refine ⟨329958357878725355030033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219972238585816903353355 329958357878725355030033)
              ·
                refine ⟨247468768409044016272525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 329958357878725355030033 247468768409044016272525)
                ·
                  refine ⟨92800788153391506102197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 247468768409044016272525 92800788153391506102197)
                  ·
                    refine ⟨8700073889380453697081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 92800788153391506102197 8700073889380453697081)
                    ·
                      rfl

theorem cell23_50830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 3, 5].length) (baseStart_50830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_50830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_50830 prefixEnd_50830 := by exact prefixLift 50830
  have htrace : WordTrace (prefixWord ++ tailWord_50830) baseStart_50830 baseEnd_50830 := by
    simpa [prefixWord, tailWord_50830, baseEnd_50830] using wordTrace_append hprefix tailTrace_50830
  have hstable : (prefixWord ++ tailWord_50830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50830).length < 2 ^ (prefixWord ++ tailWord_50830).sum := by decide
  have hdescent : baseEnd_50830 < baseStart_50830 := by decide
  rcases family_descends (prefixWord ++ tailWord_50830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50844 : List Nat := [2, 2, 3, 2, 3, 1, 1, 2, 3, 1, 3]
def baseStart_50844 : Nat := 118140960795 + 50844 * 2 ^ 59
def prefixEnd_50844 : Nat := 4983230072969 + 3 ^ 40 * 50844 * 2
def baseEnd_50844 : Nat := 26107410397304306316179

theorem tailTrace_50844 : CollatzResearch.WordTrace tailWord_50844 prefixEnd_50844 26107410397304306316179 := by
  unfold tailWord_50844
  simp only [CollatzResearch.WordTrace]
  refine ⟨927216513904173154491793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1236288685205564205989057 927216513904173154491793)
  ·
    refine ⟨695412385428129865868845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 927216513904173154491793 695412385428129865868845)
    ·
      refine ⟨260779644535548699700817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 695412385428129865868845 260779644535548699700817)
      ·
        refine ⟨195584733401661524775613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260779644535548699700817 195584733401661524775613)
        ·
          refine ⟨73344275025623071790855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 195584733401661524775613 73344275025623071790855)
          ·
            refine ⟨110016412538434607686283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73344275025623071790855 110016412538434607686283)
            ·
              refine ⟨165024618807651911529425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110016412538434607686283 165024618807651911529425)
              ·
                refine ⟨123768464105738933647069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165024618807651911529425 123768464105738933647069)
                ·
                  refine ⟨46413174039652100117651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123768464105738933647069 46413174039652100117651)
                  ·
                    refine ⟨69619761059478150176477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46413174039652100117651 69619761059478150176477)
                    ·
                      refine ⟨26107410397304306316179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 69619761059478150176477 26107410397304306316179)
                      ·
                        rfl

theorem cell23_50844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_50844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_50844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_50844 prefixEnd_50844 := by exact prefixLift 50844
  have htrace : WordTrace (prefixWord ++ tailWord_50844) baseStart_50844 baseEnd_50844 := by
    simpa [prefixWord, tailWord_50844, baseEnd_50844] using wordTrace_append hprefix tailTrace_50844
  have hstable : (prefixWord ++ tailWord_50844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50844).length < 2 ^ (prefixWord ++ tailWord_50844).sum := by decide
  have hdescent : baseEnd_50844 < baseStart_50844 := by decide
  rcases family_descends (prefixWord ++ tailWord_50844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50861 : List Nat := [1, 5, 2, 1, 1, 1, 4, 3, 1, 1, 3]
def baseStart_50861 : Nat := 118140960795 + 50861 * 2 ^ 59
def prefixEnd_50861 : Nat := 4983230072969 + 3 ^ 40 * 50861 * 2
def baseEnd_50861 : Nat := 26116139568430739803601

theorem tailTrace_50861 : CollatzResearch.WordTrace tailWord_50861 prefixEnd_50861 26116139568430739803601 := by
  unfold tailWord_50861
  simp only [CollatzResearch.WordTrace]
  refine ⟨1855053068746758212352437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1236702045831172141568291 1855053068746758212352437)
  ·
    refine ⟨173911225195008582408041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1855053068746758212352437 173911225195008582408041)
    ·
      refine ⟨130433418896256436806031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173911225195008582408041 130433418896256436806031)
      ·
        refine ⟨195650128344384655209047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130433418896256436806031 195650128344384655209047)
        ·
          refine ⟨293475192516576982813571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195650128344384655209047 293475192516576982813571)
          ·
            refine ⟨440212788774865474220357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293475192516576982813571 440212788774865474220357)
            ·
              refine ⟨82539897895287276416317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 440212788774865474220357 82539897895287276416317)
              ·
                refine ⟨30952461710732728656119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82539897895287276416317 30952461710732728656119)
                ·
                  refine ⟨46428692566099092984179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30952461710732728656119 46428692566099092984179)
                  ·
                    refine ⟨69643038849148639476269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46428692566099092984179 69643038849148639476269)
                    ·
                      refine ⟨26116139568430739803601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 69643038849148639476269 26116139568430739803601)
                      ·
                        rfl

theorem cell23_50861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 3, 1, 1, 3].length) (baseStart_50861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_50861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_50861 prefixEnd_50861 := by exact prefixLift 50861
  have htrace : WordTrace (prefixWord ++ tailWord_50861) baseStart_50861 baseEnd_50861 := by
    simpa [prefixWord, tailWord_50861, baseEnd_50861] using wordTrace_append hprefix tailTrace_50861
  have hstable : (prefixWord ++ tailWord_50861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50861).length < 2 ^ (prefixWord ++ tailWord_50861).sum := by decide
  have hdescent : baseEnd_50861 < baseStart_50861 := by decide
  rcases family_descends (prefixWord ++ tailWord_50861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50867 : List Nat := [1, 1, 1, 2, 3, 3, 1, 2, 5, 2, 2]
def baseStart_50867 : Nat := 118140960795 + 50867 * 2 ^ 59
def prefixEnd_50867 : Nat := 4983230072969 + 3 ^ 40 * 50867 * 2
def baseEnd_50867 : Nat := 26119220452357716328573

theorem tailTrace_50867 : CollatzResearch.WordTrace tailWord_50867 prefixEnd_50867 26119220452357716328573 := by
  unfold tailWord_50867
  simp only [CollatzResearch.WordTrace]
  refine ⟨1855271906725021237070855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1236847937816680824713903 1855271906725021237070855)
  ·
    refine ⟨2782907860087531855606283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1855271906725021237070855 2782907860087531855606283)
    ·
      refine ⟨4174361790131297783409425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2782907860087531855606283 4174361790131297783409425)
      ·
        refine ⟨3130771342598473337557069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4174361790131297783409425 3130771342598473337557069)
        ·
          refine ⟨1174039253474427501583901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3130771342598473337557069 1174039253474427501583901)
          ·
            refine ⟨440264720052910313093963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1174039253474427501583901 440264720052910313093963)
            ·
              refine ⟨660397080079365469640945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 440264720052910313093963 660397080079365469640945)
              ·
                refine ⟨495297810059524102230709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 660397080079365469640945 495297810059524102230709)
                ·
                  refine ⟨46434169693080384584129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 495297810059524102230709 46434169693080384584129)
                  ·
                    refine ⟨34825627269810288438097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46434169693080384584129 34825627269810288438097)
                    ·
                      refine ⟨26119220452357716328573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 34825627269810288438097 26119220452357716328573)
                      ·
                        rfl

theorem cell23_50867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 5, 2, 2].length) (baseStart_50867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_50867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_50867 prefixEnd_50867 := by exact prefixLift 50867
  have htrace : WordTrace (prefixWord ++ tailWord_50867) baseStart_50867 baseEnd_50867 := by
    simpa [prefixWord, tailWord_50867, baseEnd_50867] using wordTrace_append hprefix tailTrace_50867
  have hstable : (prefixWord ++ tailWord_50867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50867).length < 2 ^ (prefixWord ++ tailWord_50867).sum := by decide
  have hdescent : baseEnd_50867 < baseStart_50867 := by decide
  rcases family_descends (prefixWord ++ tailWord_50867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50894 : List Nat := [4, 1, 1, 1, 3, 1, 5, 1, 2, 4]
def baseStart_50894 : Nat := 118140960795 + 50894 * 2 ^ 59
def prefixEnd_50894 : Nat := 4983230072969 + 3 ^ 40 * 50894 * 2
def baseEnd_50894 : Nat := 8711028143343036896983

theorem tailTrace_50894 : CollatzResearch.WordTrace tailWord_50894 prefixEnd_50894 8711028143343036896983 := by
  unfold tailWord_50894
  simp only [CollatzResearch.WordTrace]
  refine ⟨232032084703400606037967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1237504451751469898869157 232032084703400606037967)
  ·
    refine ⟨348048127055100909056951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232032084703400606037967 348048127055100909056951)
    ·
      refine ⟨522072190582651363585427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348048127055100909056951 522072190582651363585427)
      ·
        refine ⟨783108285873977045378141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 522072190582651363585427 783108285873977045378141)
        ·
          refine ⟨293665607202741392016803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 783108285873977045378141 293665607202741392016803)
          ·
            refine ⟨440498410804112088025205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293665607202741392016803 440498410804112088025205)
            ·
              refine ⟨41296726012885508252363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 440498410804112088025205 41296726012885508252363)
              ·
                refine ⟨61945089019328262378545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41296726012885508252363 61945089019328262378545)
                ·
                  refine ⟨46458816764496196783909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61945089019328262378545 46458816764496196783909)
                  ·
                    refine ⟨8711028143343036896983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46458816764496196783909 8711028143343036896983)
                    ·
                      rfl

theorem cell23_50894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 5, 1, 2, 4].length) (baseStart_50894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_50894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_50894 prefixEnd_50894 := by exact prefixLift 50894
  have htrace : WordTrace (prefixWord ++ tailWord_50894) baseStart_50894 baseEnd_50894 := by
    simpa [prefixWord, tailWord_50894, baseEnd_50894] using wordTrace_append hprefix tailTrace_50894
  have hstable : (prefixWord ++ tailWord_50894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50894).length < 2 ^ (prefixWord ++ tailWord_50894).sum := by decide
  have hdescent : baseEnd_50894 < baseStart_50894 := by decide
  rcases family_descends (prefixWord ++ tailWord_50894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50897 : List Nat := [1, 2, 2, 1, 2, 6, 1, 1, 1, 2, 4]
def baseStart_50897 : Nat := 118140960795 + 50897 * 2 ^ 59
def prefixEnd_50897 : Nat := 4983230072969 + 3 ^ 40 * 50897 * 2
def baseEnd_50897 : Nat := 26134624871992598953435

theorem tailTrace_50897 : CollatzResearch.WordTrace tailWord_50897 prefixEnd_50897 26134624871992598953435 := by
  unfold tailWord_50897
  simp only [CollatzResearch.WordTrace]
  refine ⟨1856366096616336360662945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1237577397744224240441963 1856366096616336360662945)
  ·
    refine ⟨1392274572462252270497209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1856366096616336360662945 1392274572462252270497209)
    ·
      refine ⟨1044205929346689202872907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1392274572462252270497209 1044205929346689202872907)
      ·
        refine ⟨1566308894020033804309361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1044205929346689202872907 1566308894020033804309361)
        ·
          refine ⟨1174731670515025353232021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1566308894020033804309361 1174731670515025353232021)
          ·
            refine ⟨55065547055391813432751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1174731670515025353232021 55065547055391813432751)
            ·
              refine ⟨82598320583087720149127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55065547055391813432751 82598320583087720149127)
              ·
                refine ⟨123897480874631580223691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82598320583087720149127 123897480874631580223691)
                ·
                  refine ⟨185846221311947370335537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 123897480874631580223691 185846221311947370335537)
                  ·
                    refine ⟨139384665983960527751653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 185846221311947370335537 139384665983960527751653)
                    ·
                      refine ⟨26134624871992598953435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 139384665983960527751653 26134624871992598953435)
                      ·
                        rfl

theorem cell23_50897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 1, 1, 2, 4].length) (baseStart_50897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_50897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_50897 prefixEnd_50897 := by exact prefixLift 50897
  have htrace : WordTrace (prefixWord ++ tailWord_50897) baseStart_50897 baseEnd_50897 := by
    simpa [prefixWord, tailWord_50897, baseEnd_50897] using wordTrace_append hprefix tailTrace_50897
  have hstable : (prefixWord ++ tailWord_50897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50897).length < 2 ^ (prefixWord ++ tailWord_50897).sum := by decide
  have hdescent : baseEnd_50897 < baseStart_50897 := by decide
  rcases family_descends (prefixWord ++ tailWord_50897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50917 : List Nat := [1, 3, 1, 4, 1, 1, 1, 1, 6, 1, 3]
def baseStart_50917 : Nat := 118140960795 + 50917 * 2 ^ 59
def prefixEnd_50917 : Nat := 4983230072969 + 3 ^ 40 * 50917 * 2
def baseEnd_50917 : Nat := 26144894485082520703343

theorem tailTrace_50917 : CollatzResearch.WordTrace tailWord_50917 prefixEnd_50917 26144894485082520703343 := by
  unfold tailWord_50917
  simp only [CollatzResearch.WordTrace]
  refine ⟨1857095556543879776391005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1238063704362586517594003 1857095556543879776391005)
  ·
    refine ⟨696410833703954916146627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1857095556543879776391005 696410833703954916146627)
    ·
      refine ⟨1044616250555932374219941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 696410833703954916146627 1044616250555932374219941)
      ·
        refine ⟨195865546979237320166239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1044616250555932374219941 195865546979237320166239)
        ·
          refine ⟨293798320468855980249359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195865546979237320166239 293798320468855980249359)
          ·
            refine ⟨440697480703283970374039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293798320468855980249359 440697480703283970374039)
            ·
              refine ⟨661046221054925955561059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 440697480703283970374039 661046221054925955561059)
              ·
                refine ⟨991569331582388933341589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 661046221054925955561059 991569331582388933341589)
                ·
                  refine ⟨46479812417924481250387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 991569331582388933341589 46479812417924481250387)
                  ·
                    refine ⟨69719718626886721875581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46479812417924481250387 69719718626886721875581)
                    ·
                      refine ⟨26144894485082520703343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 69719718626886721875581 26144894485082520703343)
                      ·
                        rfl

theorem cell23_50917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_50917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_50917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_50917 prefixEnd_50917 := by exact prefixLift 50917
  have htrace : WordTrace (prefixWord ++ tailWord_50917) baseStart_50917 baseEnd_50917 := by
    simpa [prefixWord, tailWord_50917, baseEnd_50917] using wordTrace_append hprefix tailTrace_50917
  have hstable : (prefixWord ++ tailWord_50917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50917).length < 2 ^ (prefixWord ++ tailWord_50917).sum := by decide
  have hdescent : baseEnd_50917 < baseStart_50917 := by decide
  rcases family_descends (prefixWord ++ tailWord_50917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50930 : List Nat := [3, 2, 1, 3, 1, 1, 1, 2, 2, 2, 5]
def baseStart_50930 : Nat := 118140960795 + 50930 * 2 ^ 59
def prefixEnd_50930 : Nat := 4983230072969 + 3 ^ 40 * 50930 * 2
def baseEnd_50930 : Nat := 26151569733590969840783

theorem tailTrace_50930 : CollatzResearch.WordTrace tailWord_50930 prefixEnd_50930 26151569733590969840783 := by
  unfold tailWord_50930
  simp only [CollatzResearch.WordTrace]
  refine ⟨464392426374195749153561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1238379803664521997742829 464392426374195749153561)
  ·
    refine ⟨348294319780646811865171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 464392426374195749153561 348294319780646811865171)
    ·
      refine ⟨522441479670970217797757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348294319780646811865171 522441479670970217797757)
      ·
        refine ⟨195915554876613831674159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 522441479670970217797757 195915554876613831674159)
        ·
          refine ⟨293873332314920747511239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195915554876613831674159 293873332314920747511239)
          ·
            refine ⟨440809998472381121266859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293873332314920747511239 440809998472381121266859)
            ·
              refine ⟨661214997708571681900289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 440809998472381121266859 661214997708571681900289)
              ·
                refine ⟨495911248281428761425217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 661214997708571681900289 495911248281428761425217)
                ·
                  refine ⟨371933436211071571068913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 495911248281428761425217 371933436211071571068913)
                  ·
                    refine ⟨278950077158303678301685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 371933436211071571068913 278950077158303678301685)
                    ·
                      refine ⟨26151569733590969840783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 278950077158303678301685 26151569733590969840783)
                      ·
                        rfl

theorem cell23_50930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_50930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_50930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_50930 prefixEnd_50930 := by exact prefixLift 50930
  have htrace : WordTrace (prefixWord ++ tailWord_50930) baseStart_50930 baseEnd_50930 := by
    simpa [prefixWord, tailWord_50930, baseEnd_50930] using wordTrace_append hprefix tailTrace_50930
  have hstable : (prefixWord ++ tailWord_50930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50930).length < 2 ^ (prefixWord ++ tailWord_50930).sum := by decide
  have hdescent : baseEnd_50930 < baseStart_50930 := by decide
  rcases family_descends (prefixWord ++ tailWord_50930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50934 : List Nat := [5, 1, 1, 1, 1, 3, 2, 1, 4, 1, 3]
def baseStart_50934 : Nat := 118140960795 + 50934 * 2 ^ 59
def prefixEnd_50934 : Nat := 4983230072969 + 3 ^ 40 * 50934 * 2
def baseEnd_50934 : Nat := 26153623656208954190765

theorem tailTrace_50934 : CollatzResearch.WordTrace tailWord_50934 prefixEnd_50934 26153623656208954190765 := by
  unfold tailWord_50934
  simp only [CollatzResearch.WordTrace]
  refine ⟨116107224842643229984991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1238477064988194453173237 116107224842643229984991)
  ·
    refine ⟨174160837263964844977487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116107224842643229984991 174160837263964844977487)
    ·
      refine ⟨261241255895947267466231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174160837263964844977487 261241255895947267466231)
      ·
        refine ⟨391861883843920901199347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261241255895947267466231 391861883843920901199347)
        ·
          refine ⟨587792825765881351799021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 391861883843920901199347 587792825765881351799021)
          ·
            refine ⟨220422309662205506924633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 587792825765881351799021 220422309662205506924633)
            ·
              refine ⟨165316732246654130193475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 220422309662205506924633 165316732246654130193475)
              ·
                refine ⟨247975098369981195290213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165316732246654130193475 247975098369981195290213)
                ·
                  refine ⟨46495330944371474116915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 247975098369981195290213 46495330944371474116915)
                  ·
                    refine ⟨69742996416557211175373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46495330944371474116915 69742996416557211175373)
                    ·
                      refine ⟨26153623656208954190765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 69742996416557211175373 26153623656208954190765)
                      ·
                        rfl

theorem cell23_50934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 4, 1, 3].length) (baseStart_50934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_50934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_50934 prefixEnd_50934 := by exact prefixLift 50934
  have htrace : WordTrace (prefixWord ++ tailWord_50934) baseStart_50934 baseEnd_50934 := by
    simpa [prefixWord, tailWord_50934, baseEnd_50934] using wordTrace_append hprefix tailTrace_50934
  have hstable : (prefixWord ++ tailWord_50934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50934).length < 2 ^ (prefixWord ++ tailWord_50934).sum := by decide
  have hdescent : baseEnd_50934 < baseStart_50934 := by decide
  rcases family_descends (prefixWord ++ tailWord_50934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50940 : List Nat := [2, 2, 2, 1, 3, 1, 2, 1, 2, 3, 4]
def baseStart_50940 : Nat := 118140960795 + 50940 * 2 ^ 59
def prefixEnd_50940 : Nat := 4983230072969 + 3 ^ 40 * 50940 * 2
def baseEnd_50940 : Nat := 26156704540135930715737

theorem tailTrace_50940 : CollatzResearch.WordTrace tailWord_50940 prefixEnd_50940 26156704540135930715737 := by
  unfold tailWord_50940
  simp only [CollatzResearch.WordTrace]
  refine ⟨928967217730277352239137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1238622956973703136318849 928967217730277352239137)
  ·
    refine ⟨696725413297708014179353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 928967217730277352239137 696725413297708014179353)
    ·
      refine ⟨522544059973281010634515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 696725413297708014179353 522544059973281010634515)
      ·
        refine ⟨783816089959921515951773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 522544059973281010634515 783816089959921515951773)
        ·
          refine ⟨293931033734970568481915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 783816089959921515951773 293931033734970568481915)
          ·
            refine ⟨440896550602455852722873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293931033734970568481915 440896550602455852722873)
            ·
              refine ⟨330672412951841889542155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 440896550602455852722873 330672412951841889542155)
              ·
                refine ⟨496008619427762834313233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 330672412951841889542155 496008619427762834313233)
                ·
                  refine ⟨372006464570822125734925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 496008619427762834313233 372006464570822125734925)
                  ·
                    refine ⟨139502424214058297150597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 372006464570822125734925 139502424214058297150597)
                    ·
                      refine ⟨26156704540135930715737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 139502424214058297150597 26156704540135930715737)
                      ·
                        rfl

theorem cell23_50940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_50940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_50940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_50940 prefixEnd_50940 := by exact prefixLift 50940
  have htrace : WordTrace (prefixWord ++ tailWord_50940) baseStart_50940 baseEnd_50940 := by
    simpa [prefixWord, tailWord_50940, baseEnd_50940] using wordTrace_append hprefix tailTrace_50940
  have hstable : (prefixWord ++ tailWord_50940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50940).length < 2 ^ (prefixWord ++ tailWord_50940).sum := by decide
  have hdescent : baseEnd_50940 < baseStart_50940 := by decide
  rcases family_descends (prefixWord ++ tailWord_50940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50951 : List Nat := [1, 1, 4, 4, 2, 1, 1, 3, 2, 1, 3]
def baseStart_50951 : Nat := 118140960795 + 50951 * 2 ^ 59
def prefixEnd_50951 : Nat := 4983230072969 + 3 ^ 40 * 50951 * 2
def baseEnd_50951 : Nat := 26162352827335387678187

theorem tailTrace_50951 : CollatzResearch.WordTrace tailWord_50951 prefixEnd_50951 26162352827335387678187 := by
  unfold tailWord_50951
  simp only [CollatzResearch.WordTrace]
  refine ⟨1858335638420703583128707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1238890425613802388752471 1858335638420703583128707)
  ·
    refine ⟨2787503457631055374693061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1858335638420703583128707 2787503457631055374693061)
    ·
      refine ⟨522656898305822882754949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2787503457631055374693061 522656898305822882754949)
      ·
        refine ⟨97998168432341790516553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 522656898305822882754949 97998168432341790516553)
        ·
          refine ⟨73498626324256342887415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97998168432341790516553 73498626324256342887415)
          ·
            refine ⟨110247939486384514331123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73498626324256342887415 110247939486384514331123)
            ·
              refine ⟨165371909229576771496685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110247939486384514331123 165371909229576771496685)
              ·
                refine ⟨62014465961091289311257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 165371909229576771496685 62014465961091289311257)
                ·
                  refine ⟨46510849470818466983443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62014465961091289311257 46510849470818466983443)
                  ·
                    refine ⟨69766274206227700475165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46510849470818466983443 69766274206227700475165)
                    ·
                      refine ⟨26162352827335387678187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 69766274206227700475165 26162352827335387678187)
                      ·
                        rfl

theorem cell23_50951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_50951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_50951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_50951 prefixEnd_50951 := by exact prefixLift 50951
  have htrace : WordTrace (prefixWord ++ tailWord_50951) baseStart_50951 baseEnd_50951 := by
    simpa [prefixWord, tailWord_50951, baseEnd_50951] using wordTrace_append hprefix tailTrace_50951
  have hstable : (prefixWord ++ tailWord_50951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50951).length < 2 ^ (prefixWord ++ tailWord_50951).sum := by decide
  have hdescent : baseEnd_50951 < baseStart_50951 := by decide
  rcases family_descends (prefixWord ++ tailWord_50951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51014 : List Nat := [6, 1, 1, 2, 1, 1, 1, 1, 9]
def baseStart_51014 : Nat := 118140960795 + 51014 * 2 ^ 59
def prefixEnd_51014 : Nat := 4983230072969 + 3 ^ 40 * 51014 * 2
def baseEnd_51014 : Nat := 2910522456507626798933

theorem tailTrace_51014 : CollatzResearch.WordTrace tailWord_51014 prefixEnd_51014 2910522456507626798933 := by
  unfold tailWord_51014
  simp only [CollatzResearch.WordTrace]
  refine ⟨58144794912264541958503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1240422291461643561781397 58144794912264541958503)
  ·
    refine ⟨87217192368396812937755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58144794912264541958503 87217192368396812937755)
    ·
      refine ⟨130825788552595219406633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87217192368396812937755 130825788552595219406633)
      ·
        refine ⟨98119341414446414554975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130825788552595219406633 98119341414446414554975)
        ·
          refine ⟨147179012121669621832463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98119341414446414554975 147179012121669621832463)
          ·
            refine ⟨220768518182504432748695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147179012121669621832463 220768518182504432748695)
            ·
              refine ⟨331152777273756649123043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220768518182504432748695 331152777273756649123043)
              ·
                refine ⟨496729165910634973684565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 331152777273756649123043 496729165910634973684565)
                ·
                  refine ⟨2910522456507626798933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 496729165910634973684565 2910522456507626798933)
                  ·
                    rfl

theorem cell23_51014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_51014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_51014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_51014 prefixEnd_51014 := by exact prefixLift 51014
  have htrace : WordTrace (prefixWord ++ tailWord_51014) baseStart_51014 baseEnd_51014 := by
    simpa [prefixWord, tailWord_51014, baseEnd_51014] using wordTrace_append hprefix tailTrace_51014
  have hstable : (prefixWord ++ tailWord_51014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51014).length < 2 ^ (prefixWord ++ tailWord_51014).sum := by decide
  have hdescent : baseEnd_51014 < baseStart_51014 := by decide
  rcases family_descends (prefixWord ++ tailWord_51014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51017 : List Nat := [1, 2, 1, 1, 2, 4, 1, 2, 2, 5, 2]
def baseStart_51017 : Nat := 118140960795 + 51017 * 2 ^ 59
def prefixEnd_51017 : Nat := 4983230072969 + 3 ^ 40 * 51017 * 2
def baseEnd_51017 : Nat := 26196242550532129452883

theorem tailTrace_51017 : CollatzResearch.WordTrace tailWord_51017 prefixEnd_51017 26196242550532129452883 := by
  unfold tailWord_51017
  simp only [CollatzResearch.WordTrace]
  refine ⟨1860742856181596855031305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1240495237454397903354203 1860742856181596855031305)
  ·
    refine ⟨1395557142136197641273479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1860742856181596855031305 1395557142136197641273479)
    ·
      refine ⟨2093335713204296461910219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1395557142136197641273479 2093335713204296461910219)
      ·
        refine ⟨3140003569806444692865329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2093335713204296461910219 3140003569806444692865329)
        ·
          refine ⟨2355002677354833519648997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3140003569806444692865329 2355002677354833519648997)
          ·
            refine ⟨441563002004031284934187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2355002677354833519648997 441563002004031284934187)
            ·
              refine ⟨662344503006046927401281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 441563002004031284934187 662344503006046927401281)
              ·
                refine ⟨496758377254535195550961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 662344503006046927401281 496758377254535195550961)
                ·
                  refine ⟨372568782940901396663221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 496758377254535195550961 372568782940901396663221)
                  ·
                    refine ⟨34928323400709505937177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 372568782940901396663221 34928323400709505937177)
                    ·
                      refine ⟨26196242550532129452883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 34928323400709505937177 26196242550532129452883)
                      ·
                        rfl

theorem cell23_51017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 5, 2].length) (baseStart_51017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_51017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_51017 prefixEnd_51017 := by exact prefixLift 51017
  have htrace : WordTrace (prefixWord ++ tailWord_51017) baseStart_51017 baseEnd_51017 := by
    simpa [prefixWord, tailWord_51017, baseEnd_51017] using wordTrace_append hprefix tailTrace_51017
  have hstable : (prefixWord ++ tailWord_51017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51017).length < 2 ^ (prefixWord ++ tailWord_51017).sum := by decide
  have hdescent : baseEnd_51017 < baseStart_51017 := by decide
  rcases family_descends (prefixWord ++ tailWord_51017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51047 : List Nat := [1, 1, 5, 1, 2, 1, 2, 1, 4, 1, 4]
def baseStart_51047 : Nat := 118140960795 + 51047 * 2 ^ 59
def prefixEnd_51047 : Nat := 4983230072969 + 3 ^ 40 * 51047 * 2
def baseEnd_51047 : Nat := 26211646970167012077745

theorem tailTrace_51047 : CollatzResearch.WordTrace tailWord_51047 prefixEnd_51047 26211646970167012077745 := by
  unfold tailWord_51047
  simp only [CollatzResearch.WordTrace]
  refine ⟨1861837046072911978623395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1241224697381941319082263 1861837046072911978623395)
  ·
    refine ⟨2792755569109367967935093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1861837046072911978623395 2792755569109367967935093)
    ·
      refine ⟨261820834604003246993915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2792755569109367967935093 261820834604003246993915)
      ·
        refine ⟨392731251906004870490873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261820834604003246993915 392731251906004870490873)
        ·
          refine ⟨294548438929503652868155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 392731251906004870490873 294548438929503652868155)
          ·
            refine ⟨441822658394255479302233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294548438929503652868155 441822658394255479302233)
            ·
              refine ⟨331366993795691609476675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 441822658394255479302233 331366993795691609476675)
              ·
                refine ⟨497050490693537414215013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 331366993795691609476675 497050490693537414215013)
                ·
                  refine ⟨93196967005038265165315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 497050490693537414215013 93196967005038265165315)
                  ·
                    refine ⟨139795450507557397747973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 93196967005038265165315 139795450507557397747973)
                    ·
                      refine ⟨26211646970167012077745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 139795450507557397747973 26211646970167012077745)
                      ·
                        rfl

theorem cell23_51047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_51047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_51047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_51047 prefixEnd_51047 := by exact prefixLift 51047
  have htrace : WordTrace (prefixWord ++ tailWord_51047) baseStart_51047 baseEnd_51047 := by
    simpa [prefixWord, tailWord_51047, baseEnd_51047] using wordTrace_append hprefix tailTrace_51047
  have hstable : (prefixWord ++ tailWord_51047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51047).length < 2 ^ (prefixWord ++ tailWord_51047).sum := by decide
  have hdescent : baseEnd_51047 < baseStart_51047 := by decide
  rcases family_descends (prefixWord ++ tailWord_51047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51108 : List Nat := [2, 3, 1, 2, 1, 4, 3, 2, 1, 4]
def baseStart_51108 : Nat := 118140960795 + 51108 * 2 ^ 59
def prefixEnd_51108 : Nat := 4983230072969 + 3 ^ 40 * 51108 * 2
def baseEnd_51108 : Nat := 8747656430030424471655

theorem tailTrace_51108 : CollatzResearch.WordTrace tailWord_51108 prefixEnd_51108 8747656430030424471655 := by
  unfold tailWord_51108
  simp only [CollatzResearch.WordTrace]
  refine ⟨932030949425959698296989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1242707932567946264395985 932030949425959698296989)
  ·
    refine ⟨349511606034734886861371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 932030949425959698296989 349511606034734886861371)
    ·
      refine ⟨524267409052102330292057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349511606034734886861371 524267409052102330292057)
      ·
        refine ⟨393200556789076747719043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 524267409052102330292057 393200556789076747719043)
        ·
          refine ⟨589800835183615121578565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 393200556789076747719043 589800835183615121578565)
          ·
            refine ⟨110587656596927835295981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 589800835183615121578565 110587656596927835295981)
            ·
              refine ⟨41470371223847938235993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110587656596927835295981 41470371223847938235993)
              ·
                refine ⟨31102778417885953676995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41470371223847938235993 31102778417885953676995)
                ·
                  refine ⟨46654167626828930515493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31102778417885953676995 46654167626828930515493)
                  ·
                    refine ⟨8747656430030424471655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46654167626828930515493 8747656430030424471655)
                    ·
                      rfl

theorem cell23_51108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 3, 2, 1, 4].length) (baseStart_51108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_51108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_51108 prefixEnd_51108 := by exact prefixLift 51108
  have htrace : WordTrace (prefixWord ++ tailWord_51108) baseStart_51108 baseEnd_51108 := by
    simpa [prefixWord, tailWord_51108, baseEnd_51108] using wordTrace_append hprefix tailTrace_51108
  have hstable : (prefixWord ++ tailWord_51108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51108).length < 2 ^ (prefixWord ++ tailWord_51108).sum := by decide
  have hdescent : baseEnd_51108 < baseStart_51108 := by decide
  rcases family_descends (prefixWord ++ tailWord_51108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51120 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 10]
def baseStart_51120 : Nat := 118140960795 + 51120 * 2 ^ 59
def prefixEnd_51120 : Nat := 4983230072969 + 3 ^ 40 * 51120 * 2
def baseEnd_51120 : Nat := 26249131057945226464909

theorem tailTrace_51120 : CollatzResearch.WordTrace tailWord_51120 prefixEnd_51120 26249131057945226464909 := by
  unfold tailWord_51120
  simp only [CollatzResearch.WordTrace]
  refine ⟨932249787404222723015407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1242999716538963630687209 932249787404222723015407)
  ·
    refine ⟨1398374681106334084523111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 932249787404222723015407 1398374681106334084523111)
    ·
      refine ⟨2097562021659501126784667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1398374681106334084523111 2097562021659501126784667)
      ·
        refine ⟨3146343032489251690177001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2097562021659501126784667 3146343032489251690177001)
        ·
          refine ⟨2359757274366938767632751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3146343032489251690177001 2359757274366938767632751)
          ·
            refine ⟨3539635911550408151449127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2359757274366938767632751 3539635911550408151449127)
            ·
              refine ⟨5309453867325612227173691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3539635911550408151449127 5309453867325612227173691)
              ·
                refine ⟨7964180800988418340760537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5309453867325612227173691 7964180800988418340760537)
                ·
                  refine ⟨5973135600741313755570403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7964180800988418340760537 5973135600741313755570403)
                  ·
                    refine ⟨8959703401111970633355605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5973135600741313755570403 8959703401111970633355605)
                    ·
                      refine ⟨26249131057945226464909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 8959703401111970633355605 26249131057945226464909)
                      ·
                        rfl

theorem cell23_51120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 10].length) (baseStart_51120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_51120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_51120 prefixEnd_51120 := by exact prefixLift 51120
  have htrace : WordTrace (prefixWord ++ tailWord_51120) baseStart_51120 baseEnd_51120 := by
    simpa [prefixWord, tailWord_51120, baseEnd_51120] using wordTrace_append hprefix tailTrace_51120
  have hstable : (prefixWord ++ tailWord_51120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51120).length < 2 ^ (prefixWord ++ tailWord_51120).sum := by decide
  have hdescent : baseEnd_51120 < baseStart_51120 := by decide
  rcases family_descends (prefixWord ++ tailWord_51120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51121 : List Nat := [1, 2, 2, 4, 2, 3, 2, 1, 6]
def baseStart_51121 : Nat := 118140960795 + 51121 * 2 ^ 59
def prefixEnd_51121 : Nat := 4983230072969 + 3 ^ 40 * 51121 * 2
def baseEnd_51121 : Nat := 2916627170955524728045

theorem tailTrace_51121 : CollatzResearch.WordTrace tailWord_51121 prefixEnd_51121 2916627170955524728045 := by
  unfold tailWord_51121
  simp only [CollatzResearch.WordTrace]
  refine ⟨1864536047804822616817217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1243024031869881744544811 1864536047804822616817217)
  ·
    refine ⟨1398402035853616962612913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1864536047804822616817217 1398402035853616962612913)
    ·
      refine ⟨1048801526890212721959685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1398402035853616962612913 1048801526890212721959685)
      ·
        refine ⟨196650286291914885367441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1048801526890212721959685 196650286291914885367441)
        ·
          refine ⟨147487714718936164025581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196650286291914885367441 147487714718936164025581)
          ·
            refine ⟨55307893019601061509593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147487714718936164025581 55307893019601061509593)
            ·
              refine ⟨41480919764700796132195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55307893019601061509593 41480919764700796132195)
              ·
                refine ⟨62221379647051194198293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41480919764700796132195 62221379647051194198293)
                ·
                  refine ⟨2916627170955524728045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 62221379647051194198293 2916627170955524728045)
                  ·
                    rfl

theorem cell23_51121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 2, 1, 6].length) (baseStart_51121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_51121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_51121 prefixEnd_51121 := by exact prefixLift 51121
  have htrace : WordTrace (prefixWord ++ tailWord_51121) baseStart_51121 baseEnd_51121 := by
    simpa [prefixWord, tailWord_51121, baseEnd_51121] using wordTrace_append hprefix tailTrace_51121
  have hstable : (prefixWord ++ tailWord_51121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51121).length < 2 ^ (prefixWord ++ tailWord_51121).sum := by decide
  have hdescent : baseEnd_51121 < baseStart_51121 := by decide
  rcases family_descends (prefixWord ++ tailWord_51121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51134 : List Nat := [4, 2, 1, 1, 1, 4, 1, 1, 3, 5]
def baseStart_51134 : Nat := 118140960795 + 51134 * 2 ^ 59
def prefixEnd_51134 : Nat := 4983230072969 + 3 ^ 40 * 51134 * 2
def baseEnd_51134 : Nat := 8752106595702723896615

theorem tailTrace_51134 : CollatzResearch.WordTrace tailWord_51134 prefixEnd_51134 8752106595702723896615 := by
  unfold tailWord_51134
  simp only [CollatzResearch.WordTrace]
  refine ⟨233126274594715729630057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1243340131171817224693637 233126274594715729630057)
  ·
    refine ⟨174844705946036797222543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233126274594715729630057 174844705946036797222543)
    ·
      refine ⟨262267058919055195833815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174844705946036797222543 262267058919055195833815)
      ·
        refine ⟨393400588378582793750723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262267058919055195833815 393400588378582793750723)
        ·
          refine ⟨590100882567874190626085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 393400588378582793750723 590100882567874190626085)
          ·
            refine ⟨110643915481476410742391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 590100882567874190626085 110643915481476410742391)
            ·
              refine ⟨165965873222214616113587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110643915481476410742391 165965873222214616113587)
              ·
                refine ⟨248948809833321924170381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165965873222214616113587 248948809833321924170381)
                ·
                  refine ⟨93355803687495721563893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 248948809833321924170381 93355803687495721563893)
                  ·
                    refine ⟨8752106595702723896615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 93355803687495721563893 8752106595702723896615)
                    ·
                      rfl

theorem cell23_51134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_51134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_51134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_51134 prefixEnd_51134 := by exact prefixLift 51134
  have htrace : WordTrace (prefixWord ++ tailWord_51134) baseStart_51134 baseEnd_51134 := by
    simpa [prefixWord, tailWord_51134, baseEnd_51134] using wordTrace_append hprefix tailTrace_51134
  have hstable : (prefixWord ++ tailWord_51134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51134).length < 2 ^ (prefixWord ++ tailWord_51134).sum := by decide
  have hdescent : baseEnd_51134 < baseStart_51134 := by decide
  rcases family_descends (prefixWord ++ tailWord_51134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51147 : List Nat := [1, 1, 1, 1, 3, 4, 3, 2, 1, 6]
def baseStart_51147 : Nat := 118140960795 + 51147 * 2 ^ 59
def prefixEnd_51147 : Nat := 4983230072969 + 3 ^ 40 * 51147 * 2
def baseEnd_51147 : Nat := 8754331678538873609095

theorem tailTrace_51147 : CollatzResearch.WordTrace tailWord_51147 prefixEnd_51147 8754331678538873609095 := by
  unfold tailWord_51147
  simp only [CollatzResearch.WordTrace]
  refine ⟨1865484345710629057263695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1243656230473752704842463 1865484345710629057263695)
  ·
    refine ⟨2798226518565943585895543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1865484345710629057263695 2798226518565943585895543)
    ·
      refine ⟨4197339777848915378843315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2798226518565943585895543 4197339777848915378843315)
      ·
        refine ⟨6296009666773373068264973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4197339777848915378843315 6296009666773373068264973)
        ·
          refine ⟨2361003625040014900599365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6296009666773373068264973 2361003625040014900599365)
          ·
            refine ⟨442688179695002793862381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2361003625040014900599365 442688179695002793862381)
            ·
              refine ⟨166008067385626047698393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 442688179695002793862381 166008067385626047698393)
              ·
                refine ⟨124506050539219535773795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166008067385626047698393 124506050539219535773795)
                ·
                  refine ⟨186759075808829303660693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124506050539219535773795 186759075808829303660693)
                  ·
                    refine ⟨8754331678538873609095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 186759075808829303660693 8754331678538873609095)
                    ·
                      rfl

theorem cell23_51147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 2, 1, 6].length) (baseStart_51147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_51147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_51147 prefixEnd_51147 := by exact prefixLift 51147
  have htrace : WordTrace (prefixWord ++ tailWord_51147) baseStart_51147 baseEnd_51147 := by
    simpa [prefixWord, tailWord_51147, baseEnd_51147] using wordTrace_append hprefix tailTrace_51147
  have hstable : (prefixWord ++ tailWord_51147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51147).length < 2 ^ (prefixWord ++ tailWord_51147).sum := by decide
  have hdescent : baseEnd_51147 < baseStart_51147 := by decide
  rcases family_descends (prefixWord ++ tailWord_51147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51165 : List Nat := [1, 4, 3, 1, 3, 1, 1, 4, 1, 1, 3]
def baseStart_51165 : Nat := 118140960795 + 51165 * 2 ^ 59
def prefixEnd_51165 : Nat := 4983230072969 + 3 ^ 40 * 51165 * 2
def baseEnd_51165 : Nat := 26272237687397550402203

theorem tailTrace_51165 : CollatzResearch.WordTrace tailWord_51165 prefixEnd_51165 26272237687397550402203 := by
  unfold tailWord_51165
  simp only [CollatzResearch.WordTrace]
  refine ⟨1866140859645418131418949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1244093906430278754279299 1866140859645418131418949)
  ·
    refine ⟨349901411183515899641053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1866140859645418131418949 349901411183515899641053)
    ·
      refine ⟨131213029193818462365395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 349901411183515899641053 131213029193818462365395)
      ·
        refine ⟨196819543790727693548093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131213029193818462365395 196819543790727693548093)
        ·
          refine ⟨73807328921522885080535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196819543790727693548093 73807328921522885080535)
          ·
            refine ⟨110710993382284327620803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73807328921522885080535 110710993382284327620803)
            ·
              refine ⟨166066490073426491431205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110710993382284327620803 166066490073426491431205)
              ·
                refine ⟨31137466888767467143351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 166066490073426491431205 31137466888767467143351)
                ·
                  refine ⟨46706200333151200715027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31137466888767467143351 46706200333151200715027)
                  ·
                    refine ⟨70059300499726801072541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46706200333151200715027 70059300499726801072541)
                    ·
                      refine ⟨26272237687397550402203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 70059300499726801072541 26272237687397550402203)
                      ·
                        rfl

theorem cell23_51165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 4, 1, 1, 3].length) (baseStart_51165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_51165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_51165 prefixEnd_51165 := by exact prefixLift 51165
  have htrace : WordTrace (prefixWord ++ tailWord_51165) baseStart_51165 baseEnd_51165 := by
    simpa [prefixWord, tailWord_51165, baseEnd_51165] using wordTrace_append hprefix tailTrace_51165
  have hstable : (prefixWord ++ tailWord_51165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51165).length < 2 ^ (prefixWord ++ tailWord_51165).sum := by decide
  have hdescent : baseEnd_51165 < baseStart_51165 := by decide
  rcases family_descends (prefixWord ++ tailWord_51165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51205 : List Nat := [1, 3, 1, 1, 2, 5, 2, 3, 1, 2, 2]
def baseStart_51205 : Nat := 118140960795 + 51205 * 2 ^ 59
def prefixEnd_51205 : Nat := 4983230072969 + 3 ^ 40 * 51205 * 2
def baseEnd_51205 : Nat := 26292776913577393902019

theorem tailTrace_51205 : CollatzResearch.WordTrace tailWord_51205 prefixEnd_51205 26292776913577393902019 := by
  unfold tailWord_51205
  simp only [CollatzResearch.WordTrace]
  refine ⟨1867599779500504962875069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1245066519667003308583379 1867599779500504962875069)
  ·
    refine ⟨700349917312689361078151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1867599779500504962875069 700349917312689361078151)
    ·
      refine ⟨1050524875969034041617227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 700349917312689361078151 1050524875969034041617227)
      ·
        refine ⟨1575787313953551062425841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1050524875969034041617227 1575787313953551062425841)
        ·
          refine ⟨1181840485465163296819381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1575787313953551062425841 1181840485465163296819381)
          ·
            refine ⟨110797545512359059076817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1181840485465163296819381 110797545512359059076817)
            ·
              refine ⟨83098159134269294307613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110797545512359059076817 83098159134269294307613)
              ·
                refine ⟨31161809675350985365355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83098159134269294307613 31161809675350985365355)
                ·
                  refine ⟨46742714513026478048033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31161809675350985365355 46742714513026478048033)
                  ·
                    refine ⟨35057035884769858536025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46742714513026478048033 35057035884769858536025)
                    ·
                      refine ⟨26292776913577393902019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 35057035884769858536025 26292776913577393902019)
                      ·
                        rfl

theorem cell23_51205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 3, 1, 2, 2].length) (baseStart_51205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_51205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_51205 prefixEnd_51205 := by exact prefixLift 51205
  have htrace : WordTrace (prefixWord ++ tailWord_51205) baseStart_51205 baseEnd_51205 := by
    simpa [prefixWord, tailWord_51205, baseEnd_51205] using wordTrace_append hprefix tailTrace_51205
  have hstable : (prefixWord ++ tailWord_51205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51205).length < 2 ^ (prefixWord ++ tailWord_51205).sum := by decide
  have hdescent : baseEnd_51205 < baseStart_51205 := by decide
  rcases family_descends (prefixWord ++ tailWord_51205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51227 : List Nat := [1, 1, 1, 1, 1, 1, 3, 5, 2, 3, 4]
def baseStart_51227 : Nat := 118140960795 + 51227 * 2 ^ 59
def prefixEnd_51227 : Nat := 4983230072969 + 3 ^ 40 * 51227 * 2
def baseEnd_51227 : Nat := 26304073487976307826917

theorem tailTrace_51227 : CollatzResearch.WordTrace tailWord_51227 prefixEnd_51227 26304073487976307826917 := by
  unfold tailWord_51227
  simp only [CollatzResearch.WordTrace]
  refine ⟨1868402185420802720175935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1245601456947201813450623 1868402185420802720175935)
  ·
    refine ⟨2802603278131204080263903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1868402185420802720175935 2802603278131204080263903)
    ·
      refine ⟨4203904917196806120395855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2802603278131204080263903 4203904917196806120395855)
      ·
        refine ⟨6305857375795209180593783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4203904917196806120395855 6305857375795209180593783)
        ·
          refine ⟨9458786063692813770890675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6305857375795209180593783 9458786063692813770890675)
          ·
            refine ⟨14188179095539220656336013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9458786063692813770890675 14188179095539220656336013)
            ·
              refine ⟨5320567160827207746126005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14188179095539220656336013 5320567160827207746126005)
              ·
                refine ⟨498803171327550726199313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5320567160827207746126005 498803171327550726199313)
                ·
                  refine ⟨374102378495663044649485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 498803171327550726199313 374102378495663044649485)
                  ·
                    refine ⟨140288391935873641743557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 374102378495663044649485 140288391935873641743557)
                    ·
                      refine ⟨26304073487976307826917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 140288391935873641743557 26304073487976307826917)
                      ·
                        rfl

theorem cell23_51227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 3, 4].length) (baseStart_51227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_51227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_51227 prefixEnd_51227 := by exact prefixLift 51227
  have htrace : WordTrace (prefixWord ++ tailWord_51227) baseStart_51227 baseEnd_51227 := by
    simpa [prefixWord, tailWord_51227, baseEnd_51227] using wordTrace_append hprefix tailTrace_51227
  have hstable : (prefixWord ++ tailWord_51227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51227).length < 2 ^ (prefixWord ++ tailWord_51227).sum := by decide
  have hdescent : baseEnd_51227 < baseStart_51227 := by decide
  rcases family_descends (prefixWord ++ tailWord_51227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51248 : List Nat := [2, 1, 1, 1, 2, 6, 2, 2, 1, 3, 2]
def baseStart_51248 : Nat := 118140960795 + 51248 * 2 ^ 59
def prefixEnd_51248 : Nat := 4983230072969 + 3 ^ 40 * 51248 * 2
def baseEnd_51248 : Nat := 26314856581720725664321

theorem tailTrace_51248 : CollatzResearch.WordTrace tailWord_51248 prefixEnd_51248 26314856581720725664321 := by
  unfold tailWord_51248
  simp only [CollatzResearch.WordTrace]
  refine ⟨934584059172361653345199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1246112078896482204460265 934584059172361653345199)
  ·
    refine ⟨1401876088758542480017799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 934584059172361653345199 1401876088758542480017799)
    ·
      refine ⟨2102814133137813720026699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1401876088758542480017799 2102814133137813720026699)
      ·
        refine ⟨3154221199706720580040049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2102814133137813720026699 3154221199706720580040049)
        ·
          refine ⟨2365665899780040435030037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3154221199706720580040049 2365665899780040435030037)
          ·
            refine ⟨110890589052189395392033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 2365665899780040435030037 110890589052189395392033)
            ·
              refine ⟨83167941789142046544025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110890589052189395392033 83167941789142046544025)
              ·
                refine ⟨62375956341856534908019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83167941789142046544025 62375956341856534908019)
                ·
                  refine ⟨93563934512784802362029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62375956341856534908019 93563934512784802362029)
                  ·
                    refine ⟨35086475442294300885761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 93563934512784802362029 35086475442294300885761)
                    ·
                      refine ⟨26314856581720725664321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 35086475442294300885761 26314856581720725664321)
                      ·
                        rfl

theorem cell23_51248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 2, 1, 3, 2].length) (baseStart_51248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_51248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_51248 prefixEnd_51248 := by exact prefixLift 51248
  have htrace : WordTrace (prefixWord ++ tailWord_51248) baseStart_51248 baseEnd_51248 := by
    simpa [prefixWord, tailWord_51248, baseEnd_51248] using wordTrace_append hprefix tailTrace_51248
  have hstable : (prefixWord ++ tailWord_51248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51248).length < 2 ^ (prefixWord ++ tailWord_51248).sum := by decide
  have hdescent : baseEnd_51248 < baseStart_51248 := by decide
  rcases family_descends (prefixWord ++ tailWord_51248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51261 : List Nat := [1, 4, 1, 3, 1, 1, 2, 1, 3, 4, 2]
def baseStart_51261 : Nat := 118140960795 + 51261 * 2 ^ 59
def prefixEnd_51261 : Nat := 4983230072969 + 3 ^ 40 * 51261 * 2
def baseEnd_51261 : Nat := 26321531830229174801761

theorem tailTrace_51261 : CollatzResearch.WordTrace tailWord_51261 prefixEnd_51261 26321531830229174801761 := by
  unfold tailWord_51261
  simp only [CollatzResearch.WordTrace]
  refine ⟨1869642267297626526913637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1246428178198417684609091 1869642267297626526913637)
  ·
    refine ⟨350557925118304973796307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1869642267297626526913637 350557925118304973796307)
    ·
      refine ⟨525836887677457460694461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350557925118304973796307 525836887677457460694461)
      ·
        refine ⟨197188832879046547760423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 525836887677457460694461 197188832879046547760423)
        ·
          refine ⟨295783249318569821640635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197188832879046547760423 295783249318569821640635)
          ·
            refine ⟨443674873977854732460953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295783249318569821640635 443674873977854732460953)
            ·
              refine ⟨332756155483391049345715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 443674873977854732460953 332756155483391049345715)
              ·
                refine ⟨499134233225086574018573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 332756155483391049345715 499134233225086574018573)
                ·
                  refine ⟨187175337459407465256965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 499134233225086574018573 187175337459407465256965)
                  ·
                    refine ⟨35095375773638899735681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 187175337459407465256965 35095375773638899735681)
                    ·
                      refine ⟨26321531830229174801761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 35095375773638899735681 26321531830229174801761)
                      ·
                        rfl

theorem cell23_51261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_51261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_51261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_51261 prefixEnd_51261 := by exact prefixLift 51261
  have htrace : WordTrace (prefixWord ++ tailWord_51261) baseStart_51261 baseEnd_51261 := by
    simpa [prefixWord, tailWord_51261, baseEnd_51261] using wordTrace_append hprefix tailTrace_51261
  have hstable : (prefixWord ++ tailWord_51261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51261).length < 2 ^ (prefixWord ++ tailWord_51261).sum := by decide
  have hdescent : baseEnd_51261 < baseStart_51261 := by decide
  rcases family_descends (prefixWord ++ tailWord_51261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51264 : List Nat := [2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 5]
def baseStart_51264 : Nat := 118140960795 + 51264 * 2 ^ 59
def prefixEnd_51264 : Nat := 4983230072969 + 3 ^ 40 * 51264 * 2
def baseEnd_51264 : Nat := 26323072272192663064247

theorem tailTrace_51264 : CollatzResearch.WordTrace tailWord_51264 prefixEnd_51264 26323072272192663064247 := by
  unfold tailWord_51264
  simp only [CollatzResearch.WordTrace]
  refine ⟨934875843143379019636423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1246501124191172026181897 934875843143379019636423)
  ·
    refine ⟨1402313764715068529454635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 934875843143379019636423 1402313764715068529454635)
    ·
      refine ⟨2103470647072602794181953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1402313764715068529454635 2103470647072602794181953)
      ·
        refine ⟨1577602985304452095636465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2103470647072602794181953 1577602985304452095636465)
        ·
          refine ⟨1183202238978339071727349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1577602985304452095636465 1183202238978339071727349)
          ·
            refine ⟨110925209904219287974439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1183202238978339071727349 110925209904219287974439)
            ·
              refine ⟨166387814856328931961659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110925209904219287974439 166387814856328931961659)
              ·
                refine ⟨249581722284493397942489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166387814856328931961659 249581722284493397942489)
                ·
                  refine ⟨187186291713370048456867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 249581722284493397942489 187186291713370048456867)
                  ·
                    refine ⟨280779437570055072685301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 187186291713370048456867 280779437570055072685301)
                    ·
                      refine ⟨26323072272192663064247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 280779437570055072685301 26323072272192663064247)
                      ·
                        rfl

theorem cell23_51264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 5].length) (baseStart_51264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_51264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_51264 prefixEnd_51264 := by exact prefixLift 51264
  have htrace : WordTrace (prefixWord ++ tailWord_51264) baseStart_51264 baseEnd_51264 := by
    simpa [prefixWord, tailWord_51264, baseEnd_51264] using wordTrace_append hprefix tailTrace_51264
  have hstable : (prefixWord ++ tailWord_51264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51264).length < 2 ^ (prefixWord ++ tailWord_51264).sum := by decide
  have hdescent : baseEnd_51264 < baseStart_51264 := by decide
  rcases family_descends (prefixWord ++ tailWord_51264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51278 : List Nat := [4, 1, 1, 1, 1, 4, 2, 1, 4, 2, 2]
def baseStart_51278 : Nat := 118140960795 + 51278 * 2 ^ 59
def prefixEnd_51278 : Nat := 4983230072969 + 3 ^ 40 * 51278 * 2
def baseEnd_51278 : Nat := 26330261001355608289183

theorem tailTrace_51278 : CollatzResearch.WordTrace tailWord_51278 prefixEnd_51278 26330261001355608289183 := by
  unfold tailWord_51278
  simp only [CollatzResearch.WordTrace]
  refine ⟨233782788529504803785311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1246841538824025620188325 233782788529504803785311)
  ·
    refine ⟨350674182794257205677967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233782788529504803785311 350674182794257205677967)
    ·
      refine ⟨526011274191385808516951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350674182794257205677967 526011274191385808516951)
      ·
        refine ⟨789016911287078712775427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 526011274191385808516951 789016911287078712775427)
        ·
          refine ⟨1183525366930618069163141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 789016911287078712775427 1183525366930618069163141)
          ·
            refine ⟨221911006299490887968089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1183525366930618069163141 221911006299490887968089)
            ·
              refine ⟨166433254724618165976067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 221911006299490887968089 166433254724618165976067)
              ·
                refine ⟨249649882086927248964101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166433254724618165976067 249649882086927248964101)
                ·
                  refine ⟨46809352891298859180769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 249649882086927248964101 46809352891298859180769)
                  ·
                    refine ⟨35107014668474144385577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46809352891298859180769 35107014668474144385577)
                    ·
                      refine ⟨26330261001355608289183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 35107014668474144385577 26330261001355608289183)
                      ·
                        rfl

theorem cell23_51278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 4, 2, 2].length) (baseStart_51278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_51278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_51278 prefixEnd_51278 := by exact prefixLift 51278
  have htrace : WordTrace (prefixWord ++ tailWord_51278) baseStart_51278 baseEnd_51278 := by
    simpa [prefixWord, tailWord_51278, baseEnd_51278] using wordTrace_append hprefix tailTrace_51278
  have hstable : (prefixWord ++ tailWord_51278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51278).length < 2 ^ (prefixWord ++ tailWord_51278).sum := by decide
  have hdescent : baseEnd_51278 < baseStart_51278 := by decide
  rcases family_descends (prefixWord ++ tailWord_51278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51324 : List Nat := [2, 2, 2, 1, 1, 4, 1, 2, 1, 2, 5]
def baseStart_51324 : Nat := 118140960795 + 51324 * 2 ^ 59
def prefixEnd_51324 : Nat := 4983230072969 + 3 ^ 40 * 51324 * 2
def baseEnd_51324 : Nat := 26353881111462428313971

theorem tailTrace_51324 : CollatzResearch.WordTrace tailWord_51324 prefixEnd_51324 26353881111462428313971 := by
  unfold tailWord_51324
  simp only [CollatzResearch.WordTrace]
  refine ⟨935970033034694143228513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1247960044046258857638017 935970033034694143228513)
  ·
    refine ⟨701977524776020607421385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 935970033034694143228513 701977524776020607421385)
    ·
      refine ⟨526483143582015455566039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 701977524776020607421385 526483143582015455566039)
      ·
        refine ⟨789724715373023183349059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 526483143582015455566039 789724715373023183349059)
        ·
          refine ⟨1184587073059534775023589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 789724715373023183349059 1184587073059534775023589)
          ·
            refine ⟨222110076198662770316923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1184587073059534775023589 222110076198662770316923)
            ·
              refine ⟨333165114297994155475385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222110076198662770316923 333165114297994155475385)
              ·
                refine ⟨249873835723495616606539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 333165114297994155475385 249873835723495616606539)
                ·
                  refine ⟨374810753585243424909809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 249873835723495616606539 374810753585243424909809)
                  ·
                    refine ⟨281108065188932568682357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 374810753585243424909809 281108065188932568682357)
                    ·
                      refine ⟨26353881111462428313971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 281108065188932568682357 26353881111462428313971)
                      ·
                        rfl

theorem cell23_51324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_51324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_51324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_51324 prefixEnd_51324 := by exact prefixLift 51324
  have htrace : WordTrace (prefixWord ++ tailWord_51324) baseStart_51324 baseEnd_51324 := by
    simpa [prefixWord, tailWord_51324, baseEnd_51324] using wordTrace_append hprefix tailTrace_51324
  have hstable : (prefixWord ++ tailWord_51324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51324).length < 2 ^ (prefixWord ++ tailWord_51324).sum := by decide
  have hdescent : baseEnd_51324 < baseStart_51324 := by decide
  rcases family_descends (prefixWord ++ tailWord_51324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51361 : List Nat := [1, 2, 3, 3, 1, 2, 1, 1, 5, 4]
def baseStart_51361 : Nat := 118140960795 + 51361 * 2 ^ 59
def prefixEnd_51361 : Nat := 4983230072969 + 3 ^ 40 * 51361 * 2
def baseEnd_51361 : Nat := 8790959965226261183767

theorem tailTrace_51361 : CollatzResearch.WordTrace tailWord_51361 prefixEnd_51361 8790959965226261183767 := by
  unfold tailWord_51361
  simp only [CollatzResearch.WordTrace]
  refine ⟨1873289566935343605553937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1248859711290229070369291 1873289566935343605553937)
  ·
    refine ⟨1404967175201507704165453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1873289566935343605553937 1404967175201507704165453)
    ·
      refine ⟨526862690700565389062045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1404967175201507704165453 526862690700565389062045)
      ·
        refine ⟨197573509012712020898267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 526862690700565389062045 197573509012712020898267)
        ·
          refine ⟨296360263519068031347401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197573509012712020898267 296360263519068031347401)
          ·
            refine ⟨222270197639301023510551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 296360263519068031347401 222270197639301023510551)
            ·
              refine ⟨333405296458951535265827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222270197639301023510551 333405296458951535265827)
              ·
                refine ⟨500107944688427302898741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 333405296458951535265827 500107944688427302898741)
                ·
                  refine ⟨46885119814540059646757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 500107944688427302898741 46885119814540059646757)
                  ·
                    refine ⟨8790959965226261183767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46885119814540059646757 8790959965226261183767)
                    ·
                      rfl

theorem cell23_51361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 5, 4].length) (baseStart_51361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_51361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_51361 prefixEnd_51361 := by exact prefixLift 51361
  have htrace : WordTrace (prefixWord ++ tailWord_51361) baseStart_51361 baseEnd_51361 := by
    simpa [prefixWord, tailWord_51361, baseEnd_51361] using wordTrace_append hprefix tailTrace_51361
  have hstable : (prefixWord ++ tailWord_51361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51361).length < 2 ^ (prefixWord ++ tailWord_51361).sum := by decide
  have hdescent : baseEnd_51361 < baseStart_51361 := by decide
  rcases family_descends (prefixWord ++ tailWord_51361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51418 : List Nat := [3, 1, 1, 2, 2, 1, 4, 2, 3, 1, 3]
def baseStart_51418 : Nat := 118140960795 + 51418 * 2 ^ 59
def prefixEnd_51418 : Nat := 4983230072969 + 3 ^ 40 * 51418 * 2
def baseEnd_51418 : Nat := 26402148292985060538539

theorem tailTrace_51418 : CollatzResearch.WordTrace tailWord_51418 prefixEnd_51418 26402148292985060538539 := by
  unfold tailWord_51418
  simp only [CollatzResearch.WordTrace]
  refine ⟨468842131932210585094727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1250245685152561560252605 468842131932210585094727)
  ·
    refine ⟨703263197898315877642091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 468842131932210585094727 703263197898315877642091)
    ·
      refine ⟨1054894796847473816463137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 703263197898315877642091 1054894796847473816463137)
      ·
        refine ⟨791171097635605362347353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1054894796847473816463137 791171097635605362347353)
        ·
          refine ⟨593378323226704021760515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 791171097635605362347353 593378323226704021760515)
          ·
            refine ⟨890067484840056032640773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 593378323226704021760515 890067484840056032640773)
            ·
              refine ⟨166887653407510506120145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 890067484840056032640773 166887653407510506120145)
              ·
                refine ⟨125165740055632879590109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166887653407510506120145 125165740055632879590109)
                ·
                  refine ⟨46937152520862329846291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 125165740055632879590109 46937152520862329846291)
                  ·
                    refine ⟨70405728781293494769437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46937152520862329846291 70405728781293494769437)
                    ·
                      refine ⟨26402148292985060538539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 70405728781293494769437 26402148292985060538539)
                      ·
                        rfl

theorem cell23_51418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 2, 3, 1, 3].length) (baseStart_51418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_51418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_51418 prefixEnd_51418 := by exact prefixLift 51418
  have htrace : WordTrace (prefixWord ++ tailWord_51418) baseStart_51418 baseEnd_51418 := by
    simpa [prefixWord, tailWord_51418, baseEnd_51418] using wordTrace_append hprefix tailTrace_51418
  have hstable : (prefixWord ++ tailWord_51418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51418).length < 2 ^ (prefixWord ++ tailWord_51418).sum := by decide
  have hdescent : baseEnd_51418 < baseStart_51418 := by decide
  rcases family_descends (prefixWord ++ tailWord_51418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51428 : List Nat := [2, 3, 1, 1, 1, 2, 1, 5, 2, 3, 2]
def baseStart_51428 : Nat := 118140960795 + 51428 * 2 ^ 59
def prefixEnd_51428 : Nat := 4983230072969 + 3 ^ 40 * 51428 * 2
def baseEnd_51428 : Nat := 26407283099530021413493

theorem tailTrace_51428 : CollatzResearch.WordTrace tailWord_51428 prefixEnd_51428 26407283099530021413493 := by
  unfold tailWord_51428
  simp only [CollatzResearch.WordTrace]
  refine ⟨937866628846307024121469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1250488838461742698828625 937866628846307024121469)
  ·
    refine ⟨351699985817365134045551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 937866628846307024121469 351699985817365134045551)
    ·
      refine ⟨527549978726047701068327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351699985817365134045551 527549978726047701068327)
      ·
        refine ⟨791324968089071551602491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 527549978726047701068327 791324968089071551602491)
        ·
          refine ⟨1186987452133607327403737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 791324968089071551602491 1186987452133607327403737)
          ·
            refine ⟨890240589100205495552803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1186987452133607327403737 890240589100205495552803)
            ·
              refine ⟨1335360883650308243329205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 890240589100205495552803 1335360883650308243329205)
              ·
                refine ⟨125190082842216397812113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1335360883650308243329205 125190082842216397812113)
                ·
                  refine ⟨93892562131662298359085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125190082842216397812113 93892562131662298359085)
                  ·
                    refine ⟨35209710799373361884657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 93892562131662298359085 35209710799373361884657)
                    ·
                      refine ⟨26407283099530021413493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 35209710799373361884657 26407283099530021413493)
                      ·
                        rfl

theorem cell23_51428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 5, 2, 3, 2].length) (baseStart_51428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_51428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_51428 prefixEnd_51428 := by exact prefixLift 51428
  have htrace : WordTrace (prefixWord ++ tailWord_51428) baseStart_51428 baseEnd_51428 := by
    simpa [prefixWord, tailWord_51428, baseEnd_51428] using wordTrace_append hprefix tailTrace_51428
  have hstable : (prefixWord ++ tailWord_51428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51428).length < 2 ^ (prefixWord ++ tailWord_51428).sum := by decide
  have hdescent : baseEnd_51428 < baseStart_51428 := by decide
  rcases family_descends (prefixWord ++ tailWord_51428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51468 : List Nat := [2, 2, 1, 2, 2, 2, 3, 3, 2, 4]
def baseStart_51468 : Nat := 118140960795 + 51468 * 2 ^ 59
def prefixEnd_51468 : Nat := 4983230072969 + 3 ^ 40 * 51468 * 2
def baseEnd_51468 : Nat := 8809274108569954971103

theorem tailTrace_51468 : CollatzResearch.WordTrace tailWord_51468 prefixEnd_51468 8809274108569954971103 := by
  unfold tailWord_51468
  simp only [CollatzResearch.WordTrace]
  refine ⟨938596088773850439849529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1251461451698467253132705 938596088773850439849529)
  ·
    refine ⟨703947066580387829887147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 938596088773850439849529 703947066580387829887147)
    ·
      refine ⟨1055920599870581744830721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 703947066580387829887147 1055920599870581744830721)
      ·
        refine ⟨791940449902936308623041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1055920599870581744830721 791940449902936308623041)
        ·
          refine ⟨593955337427202231467281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 791940449902936308623041 593955337427202231467281)
          ·
            refine ⟨445466503070401673600461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 593955337427202231467281 445466503070401673600461)
            ·
              refine ⟨167049938651400627600173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 445466503070401673600461 167049938651400627600173)
              ·
                refine ⟨62643726994275235350065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 167049938651400627600173 62643726994275235350065)
                ·
                  refine ⟨46982795245706426512549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62643726994275235350065 46982795245706426512549)
                  ·
                    refine ⟨8809274108569954971103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46982795245706426512549 8809274108569954971103)
                    ·
                      rfl

theorem cell23_51468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 3, 2, 4].length) (baseStart_51468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_51468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_51468 prefixEnd_51468 := by exact prefixLift 51468
  have htrace : WordTrace (prefixWord ++ tailWord_51468) baseStart_51468 baseEnd_51468 := by
    simpa [prefixWord, tailWord_51468, baseEnd_51468] using wordTrace_append hprefix tailTrace_51468
  have hstable : (prefixWord ++ tailWord_51468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51468).length < 2 ^ (prefixWord ++ tailWord_51468).sum := by decide
  have hdescent : baseEnd_51468 < baseStart_51468 := by decide
  rcases family_descends (prefixWord ++ tailWord_51468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51488 : List Nat := [2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 4]
def baseStart_51488 : Nat := 118140960795 + 51488 * 2 ^ 59
def prefixEnd_51488 : Nat := 4983230072969 + 3 ^ 40 * 51488 * 2
def baseEnd_51488 : Nat := 26438091938799786663217

theorem tailTrace_51488 : CollatzResearch.WordTrace tailWord_51488 prefixEnd_51488 26438091938799786663217 := by
  unfold tailWord_51488
  simp only [CollatzResearch.WordTrace]
  refine ⟨938960818737622147713559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1251947758316829530284745 938960818737622147713559)
  ·
    refine ⟨1408441228106433221570339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 938960818737622147713559 1408441228106433221570339)
    ·
      refine ⟨2112661842159649832355509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1408441228106433221570339 2112661842159649832355509)
      ·
        refine ⟨198062047702467171783329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2112661842159649832355509 198062047702467171783329)
        ·
          refine ⟨148546535776850378837497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198062047702467171783329 148546535776850378837497)
          ·
            refine ⟨111409901832637784128123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148546535776850378837497 111409901832637784128123)
            ·
              refine ⟨167114852748956676192185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111409901832637784128123 167114852748956676192185)
              ·
                refine ⟨125336139561717507144139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167114852748956676192185 125336139561717507144139)
                ·
                  refine ⟨188004209342576260716209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125336139561717507144139 188004209342576260716209)
                  ·
                    refine ⟨141003157006932195537157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 188004209342576260716209 141003157006932195537157)
                    ·
                      refine ⟨26438091938799786663217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 141003157006932195537157 26438091938799786663217)
                      ·
                        rfl

theorem cell23_51488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_51488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_51488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_51488 prefixEnd_51488 := by exact prefixLift 51488
  have htrace : WordTrace (prefixWord ++ tailWord_51488) baseStart_51488 baseEnd_51488 := by
    simpa [prefixWord, tailWord_51488, baseEnd_51488] using wordTrace_append hprefix tailTrace_51488
  have hstable : (prefixWord ++ tailWord_51488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51488).length < 2 ^ (prefixWord ++ tailWord_51488).sum := by decide
  have hdescent : baseEnd_51488 < baseStart_51488 := by decide
  rcases family_descends (prefixWord ++ tailWord_51488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51498 : List Nat := [3, 1, 4, 2, 3, 10]
def baseStart_51498 : Nat := 118140960795 + 51498 * 2 ^ 59
def prefixEnd_51498 : Nat := 4983230072969 + 3 ^ 40 * 51498 * 2
def baseEnd_51498 : Nat := 108819863149566862297

theorem tailTrace_51498 : CollatzResearch.WordTrace tailWord_51498 prefixEnd_51498 108819863149566862297 := by
  unfold tailWord_51498
  simp only [CollatzResearch.WordTrace]
  refine ⟨469571591859754000822787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1252190911626010668860765 469571591859754000822787)
  ·
    refine ⟨704357387789631001234181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 469571591859754000822787 704357387789631001234181)
    ·
      refine ⟨132067010210555812731409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 704357387789631001234181 132067010210555812731409)
      ·
        refine ⟨99050257657916859548557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132067010210555812731409 99050257657916859548557)
        ·
          refine ⟨37143846621718822330709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99050257657916859548557 37143846621718822330709)
          ·
            refine ⟨108819863149566862297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 37143846621718822330709 108819863149566862297)
            ·
              rfl

theorem cell23_51498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 10].length) (baseStart_51498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_51498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_51498 prefixEnd_51498 := by exact prefixLift 51498
  have htrace : WordTrace (prefixWord ++ tailWord_51498) baseStart_51498 baseEnd_51498 := by
    simpa [prefixWord, tailWord_51498, baseEnd_51498] using wordTrace_append hprefix tailTrace_51498
  have hstable : (prefixWord ++ tailWord_51498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51498).length < 2 ^ (prefixWord ++ tailWord_51498).sum := by decide
  have hdescent : baseEnd_51498 < baseStart_51498 := by decide
  rcases family_descends (prefixWord ++ tailWord_51498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51551 : List Nat := [1, 1, 2, 3, 1, 2, 2, 3, 2, 1, 5]
def baseStart_51551 : Nat := 118140960795 + 51551 * 2 ^ 59
def prefixEnd_51551 : Nat := 4983230072969 + 3 ^ 40 * 51551 * 2
def baseEnd_51551 : Nat := 26470441220033040175427

theorem tailTrace_51551 : CollatzResearch.WordTrace tailWord_51551 prefixEnd_51551 26470441220033040175427 := by
  unfold tailWord_51551
  simp only [CollatzResearch.WordTrace]
  refine ⟨1880219436247006054970507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1253479624164670703313671 1880219436247006054970507)
  ·
    refine ⟨2820329154370509082455761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1880219436247006054970507 2820329154370509082455761)
    ·
      refine ⟨2115246865777881811841821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2820329154370509082455761 2115246865777881811841821)
      ·
        refine ⟨793217574666705679440683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2115246865777881811841821 793217574666705679440683)
        ·
          refine ⟨1189826362000058519161025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 793217574666705679440683 1189826362000058519161025)
          ·
            refine ⟨892369771500043889370769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1189826362000058519161025 892369771500043889370769)
            ·
              refine ⟨669277328625032917028077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 892369771500043889370769 669277328625032917028077)
              ·
                refine ⟨250978998234387343885529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 669277328625032917028077 250978998234387343885529)
                ·
                  refine ⟨188234248675790507914147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 250978998234387343885529 188234248675790507914147)
                  ·
                    refine ⟨282351373013685761871221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 188234248675790507914147 282351373013685761871221)
                    ·
                      refine ⟨26470441220033040175427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 282351373013685761871221 26470441220033040175427)
                      ·
                        rfl

theorem cell23_51551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_51551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_51551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_51551 prefixEnd_51551 := by exact prefixLift 51551
  have htrace : WordTrace (prefixWord ++ tailWord_51551) baseStart_51551 baseEnd_51551 := by
    simpa [prefixWord, tailWord_51551, baseEnd_51551] using wordTrace_append hprefix tailTrace_51551
  have hstable : (prefixWord ++ tailWord_51551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51551).length < 2 ^ (prefixWord ++ tailWord_51551).sum := by decide
  have hdescent : baseEnd_51551 < baseStart_51551 := by decide
  rcases family_descends (prefixWord ++ tailWord_51551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51552 : List Nat := [2, 1, 1, 3, 5, 1, 1, 3, 1, 3, 2]
def baseStart_51552 : Nat := 118140960795 + 51552 * 2 ^ 59
def prefixEnd_51552 : Nat := 4983230072969 + 3 ^ 40 * 51552 * 2
def baseEnd_51552 : Nat := 26470954700687536262923

theorem tailTrace_51552 : CollatzResearch.WordTrace tailWord_51552 prefixEnd_51552 26470954700687536262923 := by
  unfold tailWord_51552
  simp only [CollatzResearch.WordTrace]
  refine ⟨940127954621691612878455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1253503939495588817171273 940127954621691612878455)
  ·
    refine ⟨1410191931932537419317683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 940127954621691612878455 1410191931932537419317683)
    ·
      refine ⟨2115287897898806128976525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1410191931932537419317683 2115287897898806128976525)
      ·
        refine ⟨793232961712052298366197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2115287897898806128976525 793232961712052298366197)
        ·
          refine ⟨74365590160504902971831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 793232961712052298366197 74365590160504902971831)
          ·
            refine ⟨111548385240757354457747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74365590160504902971831 111548385240757354457747)
            ·
              refine ⟨167322577861136031686621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111548385240757354457747 167322577861136031686621)
              ·
                refine ⟨62745966697926011882483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 167322577861136031686621 62745966697926011882483)
                ·
                  refine ⟨94118950046889017823725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62745966697926011882483 94118950046889017823725)
                  ·
                    refine ⟨35294606267583381683897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 94118950046889017823725 35294606267583381683897)
                    ·
                      refine ⟨26470954700687536262923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 35294606267583381683897 26470954700687536262923)
                      ·
                        rfl

theorem cell23_51552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 3, 1, 3, 2].length) (baseStart_51552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_51552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_51552 prefixEnd_51552 := by exact prefixLift 51552
  have htrace : WordTrace (prefixWord ++ tailWord_51552) baseStart_51552 baseEnd_51552 := by
    simpa [prefixWord, tailWord_51552, baseEnd_51552] using wordTrace_append hprefix tailTrace_51552
  have hstable : (prefixWord ++ tailWord_51552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51552).length < 2 ^ (prefixWord ++ tailWord_51552).sum := by decide
  have hdescent : baseEnd_51552 < baseStart_51552 := by decide
  rcases family_descends (prefixWord ++ tailWord_51552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51561 : List Nat := [1, 2, 1, 1, 1, 3, 3, 1, 4, 2, 4]
def baseStart_51561 : Nat := 118140960795 + 51561 * 2 ^ 59
def prefixEnd_51561 : Nat := 4983230072969 + 3 ^ 40 * 51561 * 2
def baseEnd_51561 : Nat := 26475576026578001050381

theorem tailTrace_51561 : CollatzResearch.WordTrace tailWord_51561 prefixEnd_51561 26475576026578001050381 := by
  unfold tailWord_51561
  simp only [CollatzResearch.WordTrace]
  refine ⟨1880584166210777762834537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1253722777473851841889691 1880584166210777762834537)
  ·
    refine ⟨1410438124658083322125903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1880584166210777762834537 1410438124658083322125903)
    ·
      refine ⟨2115657186987124983188855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1410438124658083322125903 2115657186987124983188855)
      ·
        refine ⟨3173485780480687474783283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2115657186987124983188855 3173485780480687474783283)
        ·
          refine ⟨4760228670721031212174925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3173485780480687474783283 4760228670721031212174925)
          ·
            refine ⟨1785085751520386704565597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4760228670721031212174925 1785085751520386704565597)
            ·
              refine ⟨669407156820145014212099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1785085751520386704565597 669407156820145014212099)
              ·
                refine ⟨1004110735230217521318149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 669407156820145014212099 1004110735230217521318149)
                ·
                  refine ⟨188270762855665785247153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1004110735230217521318149 188270762855665785247153)
                  ·
                    refine ⟨141203072141749338935365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 188270762855665785247153 141203072141749338935365)
                    ·
                      refine ⟨26475576026578001050381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 141203072141749338935365 26475576026578001050381)
                      ·
                        rfl

theorem cell23_51561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 4, 2, 4].length) (baseStart_51561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_51561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_51561 prefixEnd_51561 := by exact prefixLift 51561
  have htrace : WordTrace (prefixWord ++ tailWord_51561) baseStart_51561 baseEnd_51561 := by
    simpa [prefixWord, tailWord_51561, baseEnd_51561] using wordTrace_append hprefix tailTrace_51561
  have hstable : (prefixWord ++ tailWord_51561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51561).length < 2 ^ (prefixWord ++ tailWord_51561).sum := by decide
  have hdescent : baseEnd_51561 < baseStart_51561 := by decide
  rcases family_descends (prefixWord ++ tailWord_51561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51586 : List Nat := [3, 4, 2, 1, 2, 1, 2, 2, 1, 3, 2]
def baseStart_51586 : Nat := 118140960795 + 51586 * 2 ^ 59
def prefixEnd_51586 : Nat := 4983230072969 + 3 ^ 40 * 51586 * 2
def baseEnd_51586 : Nat := 26488413042940403237767

theorem tailTrace_51586 : CollatzResearch.WordTrace tailWord_51586 prefixEnd_51586 26488413042940403237767 := by
  unfold tailWord_51586
  simp only [CollatzResearch.WordTrace]
  refine ⟨470373997780051758123653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1254330660746804688329741 470373997780051758123653)
  ·
    refine ⟨88195124583759704648185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 470373997780051758123653 88195124583759704648185)
    ·
      refine ⟨66146343437819778486139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88195124583759704648185 66146343437819778486139)
      ·
        refine ⟨99219515156729667729209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66146343437819778486139 99219515156729667729209)
        ·
          refine ⟨74414636367547250796907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99219515156729667729209 74414636367547250796907)
          ·
            refine ⟨111621954551320876195361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74414636367547250796907 111621954551320876195361)
            ·
              refine ⟨83716465913490657146521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111621954551320876195361 83716465913490657146521)
              ·
                refine ⟨62787349435117992859891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83716465913490657146521 62787349435117992859891)
                ·
                  refine ⟨94181024152676989289837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62787349435117992859891 94181024152676989289837)
                  ·
                    refine ⟨35317884057253870983689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 94181024152676989289837 35317884057253870983689)
                    ·
                      refine ⟨26488413042940403237767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 35317884057253870983689 26488413042940403237767)
                      ·
                        rfl

theorem cell23_51586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_51586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_51586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_51586 prefixEnd_51586 := by exact prefixLift 51586
  have htrace : WordTrace (prefixWord ++ tailWord_51586) baseStart_51586 baseEnd_51586 := by
    simpa [prefixWord, tailWord_51586, baseEnd_51586] using wordTrace_append hprefix tailTrace_51586
  have hstable : (prefixWord ++ tailWord_51586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51586).length < 2 ^ (prefixWord ++ tailWord_51586).sum := by decide
  have hdescent : baseEnd_51586 < baseStart_51586 := by decide
  rcases family_descends (prefixWord ++ tailWord_51586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51648 : List Nat := [2, 1, 1, 2, 3, 1, 1, 3, 5, 4]
def baseStart_51648 : Nat := 118140960795 + 51648 * 2 ^ 59
def prefixEnd_51648 : Nat := 4983230072969 + 3 ^ 40 * 51648 * 2
def baseEnd_51648 : Nat := 8840082947839720220827

theorem tailTrace_51648 : CollatzResearch.WordTrace tailWord_51648 prefixEnd_51648 8840082947839720220827 := by
  unfold tailWord_51648
  simp only [CollatzResearch.WordTrace]
  refine ⟨941878658447795810625799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1255838211263727747501065 941878658447795810625799)
  ·
    refine ⟨1412817987671693715938699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 941878658447795810625799 1412817987671693715938699)
    ·
      refine ⟨2119226981507540573908049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1412817987671693715938699 2119226981507540573908049)
      ·
        refine ⟨1589420236130655430431037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2119226981507540573908049 1589420236130655430431037)
        ·
          refine ⟨596032588548995786411639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1589420236130655430431037 596032588548995786411639)
          ·
            refine ⟨894048882823493679617459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 596032588548995786411639 894048882823493679617459)
            ·
              refine ⟨1341073324235240519426189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 894048882823493679617459 1341073324235240519426189)
              ·
                refine ⟨502902496588215194784821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1341073324235240519426189 502902496588215194784821)
                ·
                  refine ⟨47147109055145174511077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 502902496588215194784821 47147109055145174511077)
                  ·
                    refine ⟨8840082947839720220827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47147109055145174511077 8840082947839720220827)
                    ·
                      rfl

theorem cell23_51648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 5, 4].length) (baseStart_51648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_51648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_51648 prefixEnd_51648 := by exact prefixLift 51648
  have htrace : WordTrace (prefixWord ++ tailWord_51648) baseStart_51648 baseEnd_51648 := by
    simpa [prefixWord, tailWord_51648, baseEnd_51648] using wordTrace_append hprefix tailTrace_51648
  have hstable : (prefixWord ++ tailWord_51648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51648).length < 2 ^ (prefixWord ++ tailWord_51648).sum := by decide
  have hdescent : baseEnd_51648 < baseStart_51648 := by decide
  rcases family_descends (prefixWord ++ tailWord_51648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51651 : List Nat := [1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 6]
def baseStart_51651 : Nat := 118140960795 + 51651 * 2 ^ 59
def prefixEnd_51651 : Nat := 4983230072969 + 3 ^ 40 * 51651 * 2
def baseEnd_51651 : Nat := 26521789285482648924967

theorem tailTrace_51651 : CollatzResearch.WordTrace tailWord_51651 prefixEnd_51651 26521789285482648924967 := by
  unfold tailWord_51651
  simp only [CollatzResearch.WordTrace]
  refine ⟨1883866735884723133610807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1255911157256482089073871 1883866735884723133610807)
  ·
    refine ⟨2825800103827084700416211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1883866735884723133610807 2825800103827084700416211)
    ·
      refine ⟨4238700155740627050624317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2825800103827084700416211 4238700155740627050624317)
      ·
        refine ⟨1589512558402735143984119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4238700155740627050624317 1589512558402735143984119)
        ·
          refine ⟨2384268837604102715976179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1589512558402735143984119 2384268837604102715976179)
          ·
            refine ⟨3576403256406154073964269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2384268837604102715976179 3576403256406154073964269)
            ·
              refine ⟨1341151221152307777736601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3576403256406154073964269 1341151221152307777736601)
              ·
                refine ⟨1005863415864230833302451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1341151221152307777736601 1005863415864230833302451)
                ·
                  refine ⟨1508795123796346249953677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1005863415864230833302451 1508795123796346249953677)
                  ·
                    refine ⟨565798171423629843732629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1508795123796346249953677 565798171423629843732629)
                    ·
                      refine ⟨26521789285482648924967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 565798171423629843732629 26521789285482648924967)
                      ·
                        rfl

theorem cell23_51651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 6].length) (baseStart_51651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_51651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_51651 prefixEnd_51651 := by exact prefixLift 51651
  have htrace : WordTrace (prefixWord ++ tailWord_51651) baseStart_51651 baseEnd_51651 := by
    simpa [prefixWord, tailWord_51651, baseEnd_51651] using wordTrace_append hprefix tailTrace_51651
  have hstable : (prefixWord ++ tailWord_51651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51651).length < 2 ^ (prefixWord ++ tailWord_51651).sum := by decide
  have hdescent : baseEnd_51651 < baseStart_51651 := by decide
  rcases family_descends (prefixWord ++ tailWord_51651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51652 : List Nat := [2, 3, 3, 2, 2, 1, 2, 1, 2, 5]
def baseStart_51652 : Nat := 118140960795 + 51652 * 2 ^ 59
def prefixEnd_51652 : Nat := 4983230072969 + 3 ^ 40 * 51652 * 2
def baseEnd_51652 : Nat := 8840767588712381670821

theorem tailTrace_51652 : CollatzResearch.WordTrace tailWord_51652 prefixEnd_51652 8840767588712381670821 := by
  unfold tailWord_51652
  simp only [CollatzResearch.WordTrace]
  refine ⟨941951604440550152198605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1255935472587400202931473 941951604440550152198605)
  ·
    refine ⟨353231851665206307074477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 941951604440550152198605 353231851665206307074477)
    ·
      refine ⟨132461944374452365152929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 353231851665206307074477 132461944374452365152929)
      ·
        refine ⟨99346458280839273864697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132461944374452365152929 99346458280839273864697)
        ·
          refine ⟨74509843710629455398523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99346458280839273864697 74509843710629455398523)
          ·
            refine ⟨111764765565944183097785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74509843710629455398523 111764765565944183097785)
            ·
              refine ⟨83823574174458137323339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111764765565944183097785 83823574174458137323339)
              ·
                refine ⟨125735361261687205985009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83823574174458137323339 125735361261687205985009)
                ·
                  refine ⟨94301520946265404488757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125735361261687205985009 94301520946265404488757)
                  ·
                    refine ⟨8840767588712381670821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 94301520946265404488757 8840767588712381670821)
                    ·
                      rfl

theorem cell23_51652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_51652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_51652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_51652 prefixEnd_51652 := by exact prefixLift 51652
  have htrace : WordTrace (prefixWord ++ tailWord_51652) baseStart_51652 baseEnd_51652 := by
    simpa [prefixWord, tailWord_51652, baseEnd_51652] using wordTrace_append hprefix tailTrace_51652
  have hstable : (prefixWord ++ tailWord_51652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51652).length < 2 ^ (prefixWord ++ tailWord_51652).sum := by decide
  have hdescent : baseEnd_51652 < baseStart_51652 := by decide
  rcases family_descends (prefixWord ++ tailWord_51652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51655 : List Nat := [1, 1, 4, 1, 1, 5, 2, 1, 2, 1, 4]
def baseStart_51655 : Nat := 118140960795 + 51655 * 2 ^ 59
def prefixEnd_51655 : Nat := 4983230072969 + 3 ^ 40 * 51655 * 2
def baseEnd_51655 : Nat := 26523843208100633274949

theorem tailTrace_51655 : CollatzResearch.WordTrace tailWord_51655 prefixEnd_51655 26523843208100633274949 := by
  unfold tailWord_51655
  simp only [CollatzResearch.WordTrace]
  refine ⟨1884012627870231816756419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1256008418580154544504279 1884012627870231816756419)
  ·
    refine ⟨2826018941805347725134629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1884012627870231816756419 2826018941805347725134629)
    ·
      refine ⟨529878551588502698462743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2826018941805347725134629 529878551588502698462743)
      ·
        refine ⟨794817827382754047694115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 529878551588502698462743 794817827382754047694115)
        ·
          refine ⟨1192226741074131071541173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 794817827382754047694115 1192226741074131071541173)
          ·
            refine ⟨111771256975699787956985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1192226741074131071541173 111771256975699787956985)
            ·
              refine ⟨83828442731774840967739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111771256975699787956985 83828442731774840967739)
              ·
                refine ⟨125742664097662261451609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83828442731774840967739 125742664097662261451609)
                ·
                  refine ⟨94306998073246696088707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125742664097662261451609 94306998073246696088707)
                  ·
                    refine ⟨141460497109870044133061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 94306998073246696088707 141460497109870044133061)
                    ·
                      refine ⟨26523843208100633274949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 141460497109870044133061 26523843208100633274949)
                      ·
                        rfl

theorem cell23_51655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 1, 2, 1, 4].length) (baseStart_51655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_51655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_51655 prefixEnd_51655 := by exact prefixLift 51655
  have htrace : WordTrace (prefixWord ++ tailWord_51655) baseStart_51655 baseEnd_51655 := by
    simpa [prefixWord, tailWord_51655, baseEnd_51655] using wordTrace_append hprefix tailTrace_51655
  have hstable : (prefixWord ++ tailWord_51655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51655).length < 2 ^ (prefixWord ++ tailWord_51655).sum := by decide
  have hdescent : baseEnd_51655 < baseStart_51655 := by decide
  rcases family_descends (prefixWord ++ tailWord_51655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51705 : List Nat := [1, 2, 1, 3, 1, 2, 3, 1, 5, 1, 3]
def baseStart_51705 : Nat := 118140960795 + 51705 * 2 ^ 59
def prefixEnd_51705 : Nat := 4983230072969 + 3 ^ 40 * 51705 * 2
def baseEnd_51705 : Nat := 26549517240825437649719

theorem tailTrace_51705 : CollatzResearch.WordTrace tailWord_51705 prefixEnd_51705 26549517240825437649719 := by
  unfold tailWord_51705
  simp only [CollatzResearch.WordTrace]
  refine ⟨1885836277689090356076569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1257224185126060237384379 1885836277689090356076569)
  ·
    refine ⟨1414377208266817767057427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1885836277689090356076569 1414377208266817767057427)
    ·
      refine ⟨2121565812400226650586141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1414377208266817767057427 2121565812400226650586141)
      ·
        refine ⟨795587179650084993969803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2121565812400226650586141 795587179650084993969803)
        ·
          refine ⟨1193380769475127490954705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 795587179650084993969803 1193380769475127490954705)
          ·
            refine ⟨895035577106345618216029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1193380769475127490954705 895035577106345618216029)
            ·
              refine ⟨335638341414879606831011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 895035577106345618216029 335638341414879606831011)
              ·
                refine ⟨503457512122319410246517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 335638341414879606831011 503457512122319410246517)
                ·
                  refine ⟨47199141761467444710611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 503457512122319410246517 47199141761467444710611)
                  ·
                    refine ⟨70798712642201167065917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47199141761467444710611 70798712642201167065917)
                    ·
                      refine ⟨26549517240825437649719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 70798712642201167065917 26549517240825437649719)
                      ·
                        rfl

theorem cell23_51705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 5, 1, 3].length) (baseStart_51705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_51705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_51705 prefixEnd_51705 := by exact prefixLift 51705
  have htrace : WordTrace (prefixWord ++ tailWord_51705) baseStart_51705 baseEnd_51705 := by
    simpa [prefixWord, tailWord_51705, baseEnd_51705] using wordTrace_append hprefix tailTrace_51705
  have hstable : (prefixWord ++ tailWord_51705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51705).length < 2 ^ (prefixWord ++ tailWord_51705).sum := by decide
  have hdescent : baseEnd_51705 < baseStart_51705 := by decide
  rcases family_descends (prefixWord ++ tailWord_51705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51715 : List Nat := [1, 1, 1, 3, 2, 1, 5, 1, 1, 5, 2]
def baseStart_51715 : Nat := 118140960795 + 51715 * 2 ^ 59
def prefixEnd_51715 : Nat := 4983230072969 + 3 ^ 40 * 51715 * 2
def baseEnd_51715 : Nat := 26554652047370398524673

theorem tailTrace_51715 : CollatzResearch.WordTrace tailWord_51715 prefixEnd_51715 26554652047370398524673 := by
  unfold tailWord_51715
  simp only [CollatzResearch.WordTrace]
  refine ⟨1886201007652862063940599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1257467338435241375960399 1886201007652862063940599)
  ·
    refine ⟨2829301511479293095910899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1886201007652862063940599 2829301511479293095910899)
    ·
      refine ⟨4243952267218939643866349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2829301511479293095910899 4243952267218939643866349)
      ·
        refine ⟨1591482100207102366449881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4243952267218939643866349 1591482100207102366449881)
        ·
          refine ⟨1193611575155326774837411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1591482100207102366449881 1193611575155326774837411)
          ·
            refine ⟨1790417362732990162256117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1193611575155326774837411 1790417362732990162256117)
            ·
              refine ⟨167851627756217827711511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1790417362732990162256117 167851627756217827711511)
              ·
                refine ⟨251777441634326741567267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167851627756217827711511 251777441634326741567267)
                ·
                  refine ⟨377666162451490112350901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 251777441634326741567267 377666162451490112350901)
                  ·
                    refine ⟨35406202729827198032897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 377666162451490112350901 35406202729827198032897)
                    ·
                      refine ⟨26554652047370398524673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 35406202729827198032897 26554652047370398524673)
                      ·
                        rfl

theorem cell23_51715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 5, 2].length) (baseStart_51715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_51715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_51715 prefixEnd_51715 := by exact prefixLift 51715
  have htrace : WordTrace (prefixWord ++ tailWord_51715) baseStart_51715 baseEnd_51715 := by
    simpa [prefixWord, tailWord_51715, baseEnd_51715] using wordTrace_append hprefix tailTrace_51715
  have hstable : (prefixWord ++ tailWord_51715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51715).length < 2 ^ (prefixWord ++ tailWord_51715).sum := by decide
  have hdescent : baseEnd_51715 < baseStart_51715 := by decide
  rcases family_descends (prefixWord ++ tailWord_51715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51738 : List Nat := [3, 1, 1, 3, 1, 1, 2, 2, 3, 6]
def baseStart_51738 : Nat := 118140960795 + 51738 * 2 ^ 59
def prefixEnd_51738 : Nat := 4983230072969 + 3 ^ 40 * 51738 * 2
def baseEnd_51738 : Nat := 8855487367474602845689

theorem tailTrace_51738 : CollatzResearch.WordTrace tailWord_51738 prefixEnd_51738 8855487367474602845689 := by
  unfold tailWord_51738
  simp only [CollatzResearch.WordTrace]
  refine ⟨471759971642384248006967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1258026591046357994685245 471759971642384248006967)
  ·
    refine ⟨707639957463576372010451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 471759971642384248006967 707639957463576372010451)
    ·
      refine ⟨1061459936195364558015677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 707639957463576372010451 1061459936195364558015677)
      ·
        refine ⟨398047476073261709255879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1061459936195364558015677 398047476073261709255879)
        ·
          refine ⟨597071214109892563883819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398047476073261709255879 597071214109892563883819)
          ·
            refine ⟨895606821164838845825729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 597071214109892563883819 895606821164838845825729)
            ·
              refine ⟨671705115873629134369297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 895606821164838845825729 671705115873629134369297)
              ·
                refine ⟨503778836905221850776973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 671705115873629134369297 503778836905221850776973)
                ·
                  refine ⟨188917063839458194041365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 503778836905221850776973 188917063839458194041365)
                  ·
                    refine ⟨8855487367474602845689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 188917063839458194041365 8855487367474602845689)
                    ·
                      rfl

theorem cell23_51738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 3, 6].length) (baseStart_51738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_51738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_51738 prefixEnd_51738 := by exact prefixLift 51738
  have htrace : WordTrace (prefixWord ++ tailWord_51738) baseStart_51738 baseEnd_51738 := by
    simpa [prefixWord, tailWord_51738, baseEnd_51738] using wordTrace_append hprefix tailTrace_51738
  have hstable : (prefixWord ++ tailWord_51738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51738).length < 2 ^ (prefixWord ++ tailWord_51738).sum := by decide
  have hdescent : baseEnd_51738 < baseStart_51738 := by decide
  rcases family_descends (prefixWord ++ tailWord_51738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51755 : List Nat := [1, 1, 1, 1, 2, 1, 3, 7, 2, 4]
def baseStart_51755 : Nat := 118140960795 + 51755 * 2 ^ 59
def prefixEnd_51755 : Nat := 4983230072969 + 3 ^ 40 * 51755 * 2
def baseEnd_51755 : Nat := 8858397091183414008163

theorem tailTrace_51755 : CollatzResearch.WordTrace tailWord_51755 prefixEnd_51755 8858397091183414008163 := by
  unfold tailWord_51755
  simp only [CollatzResearch.WordTrace]
  refine ⟨1887659927507948895396719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1258439951671965930264479 1887659927507948895396719)
  ·
    refine ⟨2831489891261923343095079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1887659927507948895396719 2831489891261923343095079)
    ·
      refine ⟨4247234836892885014642619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2831489891261923343095079 4247234836892885014642619)
      ·
        refine ⟨6370852255339327521963929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4247234836892885014642619 6370852255339327521963929)
        ·
          refine ⟨4778139191504495641472947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6370852255339327521963929 4778139191504495641472947)
          ·
            refine ⟨7167208787256743462209421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4778139191504495641472947 7167208787256743462209421)
            ·
              refine ⟨2687703295221278798328533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7167208787256743462209421 2687703295221278798328533)
              ·
                refine ⟨62993045981748721835825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2687703295221278798328533 62993045981748721835825)
                ·
                  refine ⟨47244784486311541376869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62993045981748721835825 47244784486311541376869)
                  ·
                    refine ⟨8858397091183414008163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47244784486311541376869 8858397091183414008163)
                    ·
                      rfl

theorem cell23_51755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 7, 2, 4].length) (baseStart_51755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_51755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_51755 prefixEnd_51755 := by exact prefixLift 51755
  have htrace : WordTrace (prefixWord ++ tailWord_51755) baseStart_51755 baseEnd_51755 := by
    simpa [prefixWord, tailWord_51755, baseEnd_51755] using wordTrace_append hprefix tailTrace_51755
  have hstable : (prefixWord ++ tailWord_51755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51755).length < 2 ^ (prefixWord ++ tailWord_51755).sum := by decide
  have hdescent : baseEnd_51755 < baseStart_51755 := by decide
  rcases family_descends (prefixWord ++ tailWord_51755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51768 : List Nat := [2, 1, 2, 1, 4, 1, 3, 9]
def baseStart_51768 : Nat := 118140960795 + 51768 * 2 ^ 59
def prefixEnd_51768 : Nat := 4983230072969 + 3 ^ 40 * 51768 * 2
def baseEnd_51768 : Nat := 984513574891062635627

theorem tailTrace_51768 : CollatzResearch.WordTrace tailWord_51768 prefixEnd_51768 984513574891062635627 := by
  unfold tailWord_51768
  simp only [CollatzResearch.WordTrace]
  refine ⟨944067038230426057809979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1258756050973901410413305 944067038230426057809979)
  ·
    refine ⟨1416100557345639086714969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 944067038230426057809979 1416100557345639086714969)
    ·
      refine ⟨1062075418009229315036227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1416100557345639086714969 1062075418009229315036227)
      ·
        refine ⟨1593113127013843972554341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1062075418009229315036227 1593113127013843972554341)
        ·
          refine ⟨298708711315095744853939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1593113127013843972554341 298708711315095744853939)
          ·
            refine ⟨448063066972643617280909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298708711315095744853939 448063066972643617280909)
            ·
              refine ⟨168023650114741356480341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 448063066972643617280909 168023650114741356480341)
              ·
                refine ⟨984513574891062635627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 168023650114741356480341 984513574891062635627)
                ·
                  rfl

theorem cell23_51768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 9].length) (baseStart_51768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_51768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_51768 prefixEnd_51768 := by exact prefixLift 51768
  have htrace : WordTrace (prefixWord ++ tailWord_51768) baseStart_51768 baseEnd_51768 := by
    simpa [prefixWord, tailWord_51768, baseEnd_51768] using wordTrace_append hprefix tailTrace_51768
  have hstable : (prefixWord ++ tailWord_51768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51768).length < 2 ^ (prefixWord ++ tailWord_51768).sum := by decide
  have hdescent : baseEnd_51768 < baseStart_51768 := by decide
  rcases family_descends (prefixWord ++ tailWord_51768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51796 : List Nat := [2, 4, 1, 1, 1, 5, 1, 1, 3, 2, 2]
def baseStart_51796 : Nat := 118140960795 + 51796 * 2 ^ 59
def prefixEnd_51796 : Nat := 4983230072969 + 3 ^ 40 * 51796 * 2
def baseEnd_51796 : Nat := 26596243980384581611801

theorem tailTrace_51796 : CollatzResearch.WordTrace tailWord_51796 prefixEnd_51796 26596243980384581611801 := by
  unfold tailWord_51796
  simp only [CollatzResearch.WordTrace]
  refine ⟨944577660179706448819621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1259436880239608598426161 944577660179706448819621)
  ·
    refine ⟨177108311283694959153679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 944577660179706448819621 177108311283694959153679)
    ·
      refine ⟨265662466925542438730519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177108311283694959153679 265662466925542438730519)
      ·
        refine ⟨398493700388313658095779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265662466925542438730519 398493700388313658095779)
        ·
          refine ⟨597740550582470487143669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398493700388313658095779 597740550582470487143669)
          ·
            refine ⟨56038176617106608169719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 597740550582470487143669 56038176617106608169719)
            ·
              refine ⟨84057264925659912254579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56038176617106608169719 84057264925659912254579)
              ·
                refine ⟨126085897388489868381869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84057264925659912254579 126085897388489868381869)
                ·
                  refine ⟨47282211520683700643201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126085897388489868381869 47282211520683700643201)
                  ·
                    refine ⟨35461658640512775482401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47282211520683700643201 35461658640512775482401)
                    ·
                      refine ⟨26596243980384581611801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 35461658640512775482401 26596243980384581611801)
                      ·
                        rfl

theorem cell23_51796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 1, 3, 2, 2].length) (baseStart_51796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_51796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_51796 prefixEnd_51796 := by exact prefixLift 51796
  have htrace : WordTrace (prefixWord ++ tailWord_51796) baseStart_51796 baseEnd_51796 := by
    simpa [prefixWord, tailWord_51796, baseEnd_51796] using wordTrace_append hprefix tailTrace_51796
  have hstable : (prefixWord ++ tailWord_51796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51796).length < 2 ^ (prefixWord ++ tailWord_51796).sum := by decide
  have hdescent : baseEnd_51796 < baseStart_51796 := by decide
  rcases family_descends (prefixWord ++ tailWord_51796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51816 : List Nat := [2, 1, 4, 3, 2, 2, 1, 2, 1, 2, 3]
def baseStart_51816 : Nat := 118140960795 + 51816 * 2 ^ 59
def prefixEnd_51816 : Nat := 4983230072969 + 3 ^ 40 * 51816 * 2
def baseEnd_51816 : Nat := 26606513593474503361709

theorem tailTrace_51816 : CollatzResearch.WordTrace tailWord_51816 prefixEnd_51816 26606513593474503361709 := by
  unfold tailWord_51816
  simp only [CollatzResearch.WordTrace]
  refine ⟨944942390143478156683651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1259923186857970875578201 944942390143478156683651)
  ·
    refine ⟨1417413585215217235025477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 944942390143478156683651 1417413585215217235025477)
    ·
      refine ⟨265765047227853231567277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1417413585215217235025477 265765047227853231567277)
      ·
        refine ⟨99661892710444961837729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 265765047227853231567277 99661892710444961837729)
        ·
          refine ⟨74746419532833721378297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99661892710444961837729 74746419532833721378297)
          ·
            refine ⟨56059814649625291033723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74746419532833721378297 56059814649625291033723)
            ·
              refine ⟨84089721974437936550585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56059814649625291033723 84089721974437936550585)
              ·
                refine ⟨63067291480828452412939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84089721974437936550585 63067291480828452412939)
                ·
                  refine ⟨94600937221242678619409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63067291480828452412939 94600937221242678619409)
                  ·
                    refine ⟨70950702915932008964557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 94600937221242678619409 70950702915932008964557)
                    ·
                      refine ⟨26606513593474503361709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 70950702915932008964557 26606513593474503361709)
                      ·
                        rfl

theorem cell23_51816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_51816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_51816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_51816 prefixEnd_51816 := by exact prefixLift 51816
  have htrace : WordTrace (prefixWord ++ tailWord_51816) baseStart_51816 baseEnd_51816 := by
    simpa [prefixWord, tailWord_51816, baseEnd_51816] using wordTrace_append hprefix tailTrace_51816
  have hstable : (prefixWord ++ tailWord_51816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51816).length < 2 ^ (prefixWord ++ tailWord_51816).sum := by decide
  have hdescent : baseEnd_51816 < baseStart_51816 := by decide
  rcases family_descends (prefixWord ++ tailWord_51816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51829 : List Nat := [1, 3, 4, 2, 2, 1, 1, 2, 1, 3, 3]
def baseStart_51829 : Nat := 118140960795 + 51829 * 2 ^ 59
def prefixEnd_51829 : Nat := 4983230072969 + 3 ^ 40 * 51829 * 2
def baseEnd_51829 : Nat := 26613188841982952499149

theorem tailTrace_51829 : CollatzResearch.WordTrace tailWord_51829 prefixEnd_51829 26613188841982952499149 := by
  unfold tailWord_51829
  simp only [CollatzResearch.WordTrace]
  refine ⟨1890358929239859533590541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1260239286159906355727027 1890358929239859533590541)
  ·
    refine ⟨708884598464947325096453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1890358929239859533590541 708884598464947325096453)
    ·
      refine ⟨132915862212177623455585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 708884598464947325096453 132915862212177623455585)
      ·
        refine ⟨99686896659133217591689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132915862212177623455585 99686896659133217591689)
        ·
          refine ⟨74765172494349913193767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99686896659133217591689 74765172494349913193767)
          ·
            refine ⟨112147758741524869790651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74765172494349913193767 112147758741524869790651)
            ·
              refine ⟨168221638112287304685977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112147758741524869790651 168221638112287304685977)
              ·
                refine ⟨126166228584215478514483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 168221638112287304685977 126166228584215478514483)
                ·
                  refine ⟨189249342876323217771725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126166228584215478514483 189249342876323217771725)
                  ·
                    refine ⟨70968503578621206664397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 189249342876323217771725 70968503578621206664397)
                    ·
                      refine ⟨26613188841982952499149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 70968503578621206664397 26613188841982952499149)
                      ·
                        rfl

theorem cell23_51829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_51829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_51829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_51829 prefixEnd_51829 := by exact prefixLift 51829
  have htrace : WordTrace (prefixWord ++ tailWord_51829) baseStart_51829 baseEnd_51829 := by
    simpa [prefixWord, tailWord_51829, baseEnd_51829] using wordTrace_append hprefix tailTrace_51829
  have hstable : (prefixWord ++ tailWord_51829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51829).length < 2 ^ (prefixWord ++ tailWord_51829).sum := by decide
  have hdescent : baseEnd_51829 < baseStart_51829 := by decide
  rcases family_descends (prefixWord ++ tailWord_51829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51865 : List Nat := [1, 2, 1, 2, 1, 2, 5, 1, 2, 2, 4]
def baseStart_51865 : Nat := 118140960795 + 51865 * 2 ^ 59
def prefixEnd_51865 : Nat := 4983230072969 + 3 ^ 40 * 51865 * 2
def baseEnd_51865 : Nat := 26631674145544811648983

theorem tailTrace_51865 : CollatzResearch.WordTrace tailWord_51865 prefixEnd_51865 26631674145544811648983 := by
  unfold tailWord_51865
  simp only [CollatzResearch.WordTrace]
  refine ⟨1891671957109437681901049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1261114638072958454600699 1891671957109437681901049)
  ·
    refine ⟨1418753967832078261425787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1891671957109437681901049 1418753967832078261425787)
    ·
      refine ⟨2128130951748117392138681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1418753967832078261425787 2128130951748117392138681)
      ·
        refine ⟨1596098213811088044104011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2128130951748117392138681 1596098213811088044104011)
        ·
          refine ⟨2394147320716632066156017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1596098213811088044104011 2394147320716632066156017)
          ·
            refine ⟨1795610490537474049617013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2394147320716632066156017 1795610490537474049617013)
            ·
              refine ⟨168338483487888192151595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1795610490537474049617013 168338483487888192151595)
              ·
                refine ⟨252507725231832288227393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168338483487888192151595 252507725231832288227393)
                ·
                  refine ⟨189380793923874216170545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 252507725231832288227393 189380793923874216170545)
                  ·
                    refine ⟨142035595442905662127909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 189380793923874216170545 142035595442905662127909)
                    ·
                      refine ⟨26631674145544811648983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 142035595442905662127909 26631674145544811648983)
                      ·
                        rfl

theorem cell23_51865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 2, 2, 4].length) (baseStart_51865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_51865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_51865 prefixEnd_51865 := by exact prefixLift 51865
  have htrace : WordTrace (prefixWord ++ tailWord_51865) baseStart_51865 baseEnd_51865 := by
    simpa [prefixWord, tailWord_51865, baseEnd_51865] using wordTrace_append hprefix tailTrace_51865
  have hstable : (prefixWord ++ tailWord_51865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51865).length < 2 ^ (prefixWord ++ tailWord_51865).sum := by decide
  have hdescent : baseEnd_51865 < baseStart_51865 := by decide
  rcases family_descends (prefixWord ++ tailWord_51865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51886 : List Nat := [4, 1, 4, 1, 1, 1, 2, 2, 1, 4, 2]
def baseStart_51886 : Nat := 118140960795 + 51886 * 2 ^ 59
def prefixEnd_51886 : Nat := 4983230072969 + 3 ^ 40 * 51886 * 2
def baseEnd_51886 : Nat := 26642457239289229486387

theorem tailTrace_51886 : CollatzResearch.WordTrace tailWord_51886 prefixEnd_51886 26642457239289229486387 := by
  unfold tailWord_51886
  simp only [CollatzResearch.WordTrace]
  refine ⟨236554736254169783551939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1261625260022238845610341 236554736254169783551939)
  ·
    refine ⟨354832104381254675327909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236554736254169783551939 354832104381254675327909)
    ·
      refine ⟨66531019571485251623983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 354832104381254675327909 66531019571485251623983)
      ·
        refine ⟨99796529357227877435975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66531019571485251623983 99796529357227877435975)
        ·
          refine ⟨149694794035841816153963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99796529357227877435975 149694794035841816153963)
          ·
            refine ⟨224542191053762724230945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149694794035841816153963 224542191053762724230945)
            ·
              refine ⟨168406643290322043173209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 224542191053762724230945 168406643290322043173209)
              ·
                refine ⟨126304982467741532379907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 168406643290322043173209 126304982467741532379907)
                ·
                  refine ⟨189457473701612298569861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126304982467741532379907 189457473701612298569861)
                  ·
                    refine ⟨35523276319052305981849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 189457473701612298569861 35523276319052305981849)
                    ·
                      refine ⟨26642457239289229486387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 35523276319052305981849 26642457239289229486387)
                      ·
                        rfl

theorem cell23_51886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_51886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_51886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_51886 prefixEnd_51886 := by exact prefixLift 51886
  have htrace : WordTrace (prefixWord ++ tailWord_51886) baseStart_51886 baseEnd_51886 := by
    simpa [prefixWord, tailWord_51886, baseEnd_51886] using wordTrace_append hprefix tailTrace_51886
  have hstable : (prefixWord ++ tailWord_51886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51886).length < 2 ^ (prefixWord ++ tailWord_51886).sum := by decide
  have hdescent : baseEnd_51886 < baseStart_51886 := by decide
  rcases family_descends (prefixWord ++ tailWord_51886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51902 : List Nat := [4, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3]
def baseStart_51902 : Nat := 118140960795 + 51902 * 2 ^ 59
def prefixEnd_51902 : Nat := 4983230072969 + 3 ^ 40 * 51902 * 2
def baseEnd_51902 : Nat := 26650672929761166886313

theorem tailTrace_51902 : CollatzResearch.WordTrace tailWord_51902 prefixEnd_51902 26650672929761166886313 := by
  unfold tailWord_51902
  simp only [CollatzResearch.WordTrace]
  refine ⟨236627682246924125124745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1262014305316928667331973 236627682246924125124745)
  ·
    refine ⟨177470761685193093843559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236627682246924125124745 177470761685193093843559)
    ·
      refine ⟨266206142527789640765339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177470761685193093843559 266206142527789640765339)
      ·
        refine ⟨399309213791684461148009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266206142527789640765339 399309213791684461148009)
        ·
          refine ⟨299481910343763345861007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 399309213791684461148009 299481910343763345861007)
          ·
            refine ⟨449222865515645018791511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299481910343763345861007 449222865515645018791511)
            ·
              refine ⟨673834298273467528187267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 449222865515645018791511 673834298273467528187267)
              ·
                refine ⟨1010751447410201292280901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 673834298273467528187267 1010751447410201292280901)
                ·
                  refine ⟨189515896389412742302669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1010751447410201292280901 189515896389412742302669)
                  ·
                    refine ⟨71068461146029778363501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 189515896389412742302669 71068461146029778363501)
                    ·
                      refine ⟨26650672929761166886313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 71068461146029778363501 26650672929761166886313)
                      ·
                        rfl

theorem cell23_51902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_51902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_51902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_51902 prefixEnd_51902 := by exact prefixLift 51902
  have htrace : WordTrace (prefixWord ++ tailWord_51902) baseStart_51902 baseEnd_51902 := by
    simpa [prefixWord, tailWord_51902, baseEnd_51902] using wordTrace_append hprefix tailTrace_51902
  have hstable : (prefixWord ++ tailWord_51902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51902).length < 2 ^ (prefixWord ++ tailWord_51902).sum := by decide
  have hdescent : baseEnd_51902 < baseStart_51902 := by decide
  rcases family_descends (prefixWord ++ tailWord_51902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51962 : List Nat := [3, 1, 1, 1, 1, 3, 3, 1, 4, 2, 3]
def baseStart_51962 : Nat := 118140960795 + 51962 * 2 ^ 59
def prefixEnd_51962 : Nat := 4983230072969 + 3 ^ 40 * 51962 * 2
def baseEnd_51962 : Nat := 26681481769030932136037

theorem tailTrace_51962 : CollatzResearch.WordTrace tailWord_51962 prefixEnd_51962 26681481769030932136037 := by
  unfold tailWord_51962
  simp only [CollatzResearch.WordTrace]
  refine ⟨473802459439505812045535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1263473225172015498788093 473802459439505812045535)
  ·
    refine ⟨710703689159258718068303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 473802459439505812045535 710703689159258718068303)
    ·
      refine ⟨1066055533738888077102455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 710703689159258718068303 1066055533738888077102455)
      ·
        refine ⟨1599083300608332115653683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1066055533738888077102455 1599083300608332115653683)
        ·
          refine ⟨2398624950912498173480525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1599083300608332115653683 2398624950912498173480525)
          ·
            refine ⟨899484356592186815055197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2398624950912498173480525 899484356592186815055197)
            ·
              refine ⟨337306633722070055645699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 899484356592186815055197 337306633722070055645699)
              ·
                refine ⟨505959950583105083468549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 337306633722070055645699 505959950583105083468549)
                ·
                  refine ⟨94867490734332203150353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 505959950583105083468549 94867490734332203150353)
                  ·
                    refine ⟨71150618050749152362765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 94867490734332203150353 71150618050749152362765)
                    ·
                      refine ⟨26681481769030932136037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 71150618050749152362765 26681481769030932136037)
                      ·
                        rfl

theorem cell23_51962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 4, 2, 3].length) (baseStart_51962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_51962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_51962 prefixEnd_51962 := by exact prefixLift 51962
  have htrace : WordTrace (prefixWord ++ tailWord_51962) baseStart_51962 baseEnd_51962 := by
    simpa [prefixWord, tailWord_51962, baseEnd_51962] using wordTrace_append hprefix tailTrace_51962
  have hstable : (prefixWord ++ tailWord_51962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51962).length < 2 ^ (prefixWord ++ tailWord_51962).sum := by decide
  have hdescent : baseEnd_51962 < baseStart_51962 := by decide
  rcases family_descends (prefixWord ++ tailWord_51962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51965 : List Nat := [1, 4, 1, 1, 1, 1, 3, 3, 8]
def baseStart_51965 : Nat := 118140960795 + 51965 * 2 ^ 59
def prefixEnd_51965 : Nat := 4983230072969 + 3 ^ 40 * 51965 * 2
def baseEnd_51965 : Nat := 2964780245666046710947

theorem tailTrace_51965 : CollatzResearch.WordTrace tailWord_51965 prefixEnd_51965 2964780245666046710947 := by
  unfold tailWord_51965
  simp only [CollatzResearch.WordTrace]
  refine ⟨1895319256747154760541349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1263546171164769840360899 1895319256747154760541349)
  ·
    refine ⟨355372360640091517601503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1895319256747154760541349 355372360640091517601503)
    ·
      refine ⟨533058540960137276402255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355372360640091517601503 533058540960137276402255)
      ·
        refine ⟨799587811440205914603383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 533058540960137276402255 799587811440205914603383)
        ·
          refine ⟨1199381717160308871905075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 799587811440205914603383 1199381717160308871905075)
          ·
            refine ⟨1799072575740463307857613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1199381717160308871905075 1799072575740463307857613)
            ·
              refine ⟨674652215902673740446605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1799072575740463307857613 674652215902673740446605)
              ·
                refine ⟨252994580963502652667477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 674652215902673740446605 252994580963502652667477)
                ·
                  refine ⟨2964780245666046710947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 252994580963502652667477 2964780245666046710947)
                  ·
                    rfl

theorem cell23_51965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 8].length) (baseStart_51965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_51965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_51965 prefixEnd_51965 := by exact prefixLift 51965
  have htrace : WordTrace (prefixWord ++ tailWord_51965) baseStart_51965 baseEnd_51965 := by
    simpa [prefixWord, tailWord_51965, baseEnd_51965] using wordTrace_append hprefix tailTrace_51965
  have hstable : (prefixWord ++ tailWord_51965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51965).length < 2 ^ (prefixWord ++ tailWord_51965).sum := by decide
  have hdescent : baseEnd_51965 < baseStart_51965 := by decide
  rcases family_descends (prefixWord ++ tailWord_51965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51985 : List Nat := [1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 6]
def baseStart_51985 : Nat := 118140960795 + 51985 * 2 ^ 59
def prefixEnd_51985 : Nat := 4983230072969 + 3 ^ 40 * 51985 * 2
def baseEnd_51985 : Nat := 26693291824084342148431

theorem tailTrace_51985 : CollatzResearch.WordTrace tailWord_51985 prefixEnd_51985 26693291824084342148431 := by
  unfold tailWord_51985
  simp only [CollatzResearch.WordTrace]
  refine ⟨1896048716674698176269409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1264032477783132117512939 1896048716674698176269409)
  ·
    refine ⟨1422036537506023632202057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1896048716674698176269409 1422036537506023632202057)
    ·
      refine ⟨1066527403129517724151543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1422036537506023632202057 1066527403129517724151543)
      ·
        refine ⟨1599791104694276586227315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1066527403129517724151543 1599791104694276586227315)
        ·
          refine ⟨2399686657041414879340973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1599791104694276586227315 2399686657041414879340973)
          ·
            refine ⟨899882496390530579752865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2399686657041414879340973 899882496390530579752865)
            ·
              refine ⟨674911872292897934814649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 899882496390530579752865 674911872292897934814649)
              ·
                refine ⟨506183904219673451110987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 674911872292897934814649 506183904219673451110987)
                ·
                  refine ⟨759275856329510176666481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 506183904219673451110987 759275856329510176666481)
                  ·
                    refine ⟨569456892247132632499861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 759275856329510176666481 569456892247132632499861)
                    ·
                      refine ⟨26693291824084342148431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 569456892247132632499861 26693291824084342148431)
                      ·
                        rfl

theorem cell23_51985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 6].length) (baseStart_51985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_51985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_51985 prefixEnd_51985 := by exact prefixLift 51985
  have htrace : WordTrace (prefixWord ++ tailWord_51985) baseStart_51985 baseEnd_51985 := by
    simpa [prefixWord, tailWord_51985, baseEnd_51985] using wordTrace_append hprefix tailTrace_51985
  have hstable : (prefixWord ++ tailWord_51985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51985).length < 2 ^ (prefixWord ++ tailWord_51985).sum := by decide
  have hdescent : baseEnd_51985 < baseStart_51985 := by decide
  rcases family_descends (prefixWord ++ tailWord_51985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52060 : List Nat := [2, 2, 4, 2, 1, 2, 2, 3, 1, 1, 3]
def baseStart_52060 : Nat := 118140960795 + 52060 * 2 ^ 59
def prefixEnd_52060 : Nat := 4983230072969 + 3 ^ 40 * 52060 * 2
def baseEnd_52060 : Nat := 26731802873171548710587

theorem tailTrace_52060 : CollatzResearch.WordTrace tailWord_52060 prefixEnd_52060 26731802873171548710587 := by
  unfold tailWord_52060
  simp only [CollatzResearch.WordTrace]
  refine ⟨949392095701492992624817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1265856127601990656833089 949392095701492992624817)
  ·
    refine ⟨712044071776119744468613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 949392095701492992624817 712044071776119744468613)
    ·
      refine ⟨133508263458022452087865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 712044071776119744468613 133508263458022452087865)
      ·
        refine ⟨100131197593516839065899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133508263458022452087865 100131197593516839065899)
        ·
          refine ⟨150196796390275258598849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100131197593516839065899 150196796390275258598849)
          ·
            refine ⟨112647597292706443949137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150196796390275258598849 112647597292706443949137)
            ·
              refine ⟨84485697969529832961853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112647597292706443949137 84485697969529832961853)
              ·
                refine ⟨31682136738573687360695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84485697969529832961853 31682136738573687360695)
                ·
                  refine ⟨47523205107860531041043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31682136738573687360695 47523205107860531041043)
                  ·
                    refine ⟨71284807661790796561565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47523205107860531041043 71284807661790796561565)
                    ·
                      refine ⟨26731802873171548710587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 71284807661790796561565 26731802873171548710587)
                      ·
                        rfl

theorem cell23_52060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_52060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_52060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_52060 prefixEnd_52060 := by exact prefixLift 52060
  have htrace : WordTrace (prefixWord ++ tailWord_52060) baseStart_52060 baseEnd_52060 := by
    simpa [prefixWord, tailWord_52060, baseEnd_52060] using wordTrace_append hprefix tailTrace_52060
  have hstable : (prefixWord ++ tailWord_52060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52060).length < 2 ^ (prefixWord ++ tailWord_52060).sum := by decide
  have hdescent : baseEnd_52060 < baseStart_52060 := by decide
  rcases family_descends (prefixWord ++ tailWord_52060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52072 : List Nat := [2, 1, 4, 2, 1, 3, 10]
def baseStart_52072 : Nat := 118140960795 + 52072 * 2 ^ 59
def prefixEnd_52072 : Nat := 4983230072969 + 3 ^ 40 * 52072 * 2
def baseEnd_52072 : Nat := 330098328901549404451

theorem tailTrace_52072 : CollatzResearch.WordTrace tailWord_52072 prefixEnd_52072 330098328901549404451 := by
  unfold tailWord_52072
  simp only [CollatzResearch.WordTrace]
  refine ⟨949610933679756017343235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1266147911573008023124313 949610933679756017343235)
  ·
    refine ⟨1424416400519634026014853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 949610933679756017343235 1424416400519634026014853)
    ·
      refine ⟨267078075097431379877785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1424416400519634026014853 267078075097431379877785)
      ·
        refine ⟨200308556323073534908339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267078075097431379877785 200308556323073534908339)
        ·
          refine ⟨300462834484610302362509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200308556323073534908339 300462834484610302362509)
          ·
            refine ⟨112673562931728863385941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 300462834484610302362509 112673562931728863385941)
            ·
              refine ⟨330098328901549404451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 112673562931728863385941 330098328901549404451)
              ·
                rfl

theorem cell23_52072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 10].length) (baseStart_52072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_52072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_52072 prefixEnd_52072 := by exact prefixLift 52072
  have htrace : WordTrace (prefixWord ++ tailWord_52072) baseStart_52072 baseEnd_52072 := by
    simpa [prefixWord, tailWord_52072, baseEnd_52072] using wordTrace_append hprefix tailTrace_52072
  have hstable : (prefixWord ++ tailWord_52072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52072).length < 2 ^ (prefixWord ++ tailWord_52072).sum := by decide
  have hdescent : baseEnd_52072 < baseStart_52072 := by decide
  rcases family_descends (prefixWord ++ tailWord_52072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52083 : List Nat := [1, 1, 1, 2, 2, 1, 6, 4, 1, 2, 2]
def baseStart_52083 : Nat := 118140960795 + 52083 * 2 ^ 59
def prefixEnd_52083 : Nat := 4983230072969 + 3 ^ 40 * 52083 * 2
def baseEnd_52083 : Nat := 26743612928224958722981

theorem tailTrace_52083 : CollatzResearch.WordTrace tailWord_52083 prefixEnd_52083 26743612928224958722981 := by
  unfold tailWord_52083
  simp only [CollatzResearch.WordTrace]
  refine ⟨1899623070319660913336903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1266415380213107275557935 1899623070319660913336903)
  ·
    refine ⟨2849434605479491370005355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1899623070319660913336903 2849434605479491370005355)
    ·
      refine ⟨4274151908219237055008033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2849434605479491370005355 4274151908219237055008033)
      ·
        refine ⟨3205613931164427791256025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4274151908219237055008033 3205613931164427791256025)
        ·
          refine ⟨2404210448373320843442019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3205613931164427791256025 2404210448373320843442019)
          ·
            refine ⟨3606315672559981265163029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2404210448373320843442019 3606315672559981265163029)
            ·
              refine ⟨169046047151249121804517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3606315672559981265163029 169046047151249121804517)
              ·
                refine ⟨31696133840859210338347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 169046047151249121804517 31696133840859210338347)
                ·
                  refine ⟨47544200761288815507521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31696133840859210338347 47544200761288815507521)
                  ·
                    refine ⟨35658150570966611630641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47544200761288815507521 35658150570966611630641)
                    ·
                      refine ⟨26743612928224958722981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 35658150570966611630641 26743612928224958722981)
                      ·
                        rfl

theorem cell23_52083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 4, 1, 2, 2].length) (baseStart_52083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_52083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_52083 prefixEnd_52083 := by exact prefixLift 52083
  have htrace : WordTrace (prefixWord ++ tailWord_52083) baseStart_52083 baseEnd_52083 := by
    simpa [prefixWord, tailWord_52083, baseEnd_52083] using wordTrace_append hprefix tailTrace_52083
  have hstable : (prefixWord ++ tailWord_52083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52083).length < 2 ^ (prefixWord ++ tailWord_52083).sum := by decide
  have hdescent : baseEnd_52083 < baseStart_52083 := by decide
  rcases family_descends (prefixWord ++ tailWord_52083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52086 : List Nat := [5, 1, 1, 3, 1, 2, 1, 2, 1, 1, 5]
def baseStart_52086 : Nat := 118140960795 + 52086 * 2 ^ 59
def prefixEnd_52086 : Nat := 4983230072969 + 3 ^ 40 * 52086 * 2
def baseEnd_52086 : Nat := 26745153370188446985467

theorem tailTrace_52086 : CollatzResearch.WordTrace tailWord_52086 prefixEnd_52086 26745153370188446985467 := by
  unfold tailWord_52086
  simp only [CollatzResearch.WordTrace]
  refine ⟨118733280581799526606007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1266488326205861617130741 118733280581799526606007)
  ·
    refine ⟨178099920872699289909011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118733280581799526606007 178099920872699289909011)
    ·
      refine ⟨267149881309048934863517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178099920872699289909011 267149881309048934863517)
      ·
        refine ⟨100181205490893350573819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 267149881309048934863517 100181205490893350573819)
        ·
          refine ⟨150271808236340025860729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100181205490893350573819 150271808236340025860729)
          ·
            refine ⟨112703856177255019395547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150271808236340025860729 112703856177255019395547)
            ·
              refine ⟨169055784265882529093321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112703856177255019395547 169055784265882529093321)
              ·
                refine ⟨126791838199411896819991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169055784265882529093321 126791838199411896819991)
                ·
                  refine ⟨190187757299117845229987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126791838199411896819991 190187757299117845229987)
                  ·
                    refine ⟨285281635948676767844981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 190187757299117845229987 285281635948676767844981)
                    ·
                      refine ⟨26745153370188446985467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 285281635948676767844981 26745153370188446985467)
                      ·
                        rfl

theorem cell23_52086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_52086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_52086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_52086 prefixEnd_52086 := by exact prefixLift 52086
  have htrace : WordTrace (prefixWord ++ tailWord_52086) baseStart_52086 baseEnd_52086 := by
    simpa [prefixWord, tailWord_52086, baseEnd_52086] using wordTrace_append hprefix tailTrace_52086
  have hstable : (prefixWord ++ tailWord_52086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52086).length < 2 ^ (prefixWord ++ tailWord_52086).sum := by decide
  have hdescent : baseEnd_52086 < baseStart_52086 := by decide
  rcases family_descends (prefixWord ++ tailWord_52086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52106 : List Nat := [3, 1, 2, 4, 1, 3, 2, 7]
def baseStart_52106 : Nat := 118140960795 + 52106 * 2 ^ 59
def prefixEnd_52106 : Nat := 4983230072969 + 3 ^ 40 * 52106 * 2
def baseEnd_52106 : Nat := 990941591973272916125

theorem tailTrace_52106 : CollatzResearch.WordTrace tailWord_52106 prefixEnd_52106 990941591973272916125 := by
  unfold tailWord_52106
  simp only [CollatzResearch.WordTrace]
  refine ⟨475115487309083960356043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1266974632824223894282781 475115487309083960356043)
  ·
    refine ⟨712673230963625940534065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 475115487309083960356043 712673230963625940534065)
    ·
      refine ⟨534504923222719455400549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 712673230963625940534065 534504923222719455400549)
      ·
        refine ⟨100219673104259897887603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 534504923222719455400549 100219673104259897887603)
        ·
          refine ⟨150329509656389846831405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100219673104259897887603 150329509656389846831405)
          ·
            refine ⟨56373566121146192561777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150329509656389846831405 56373566121146192561777)
            ·
              refine ⟨42280174590859644421333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56373566121146192561777 42280174590859644421333)
              ·
                refine ⟨990941591973272916125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 42280174590859644421333 990941591973272916125)
                ·
                  rfl

theorem cell23_52106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 2, 7].length) (baseStart_52106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_52106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_52106 prefixEnd_52106 := by exact prefixLift 52106
  have htrace : WordTrace (prefixWord ++ tailWord_52106) baseStart_52106 baseEnd_52106 := by
    simpa [prefixWord, tailWord_52106, baseEnd_52106] using wordTrace_append hprefix tailTrace_52106
  have hstable : (prefixWord ++ tailWord_52106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52106).length < 2 ^ (prefixWord ++ tailWord_52106).sum := by decide
  have hdescent : baseEnd_52106 < baseStart_52106 := by decide
  rcases family_descends (prefixWord ++ tailWord_52106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52116 : List Nat := [2, 4, 2, 1, 1, 1, 1, 1, 6, 1, 3]
def baseStart_52116 : Nat := 118140960795 + 52116 * 2 ^ 59
def prefixEnd_52116 : Nat := 4983230072969 + 3 ^ 40 * 52116 * 2
def baseEnd_52116 : Nat := 26760557789823329610329

theorem tailTrace_52116 : CollatzResearch.WordTrace tailWord_52116 prefixEnd_52116 26760557789823329610329 := by
  unfold tailWord_52116
  simp only [CollatzResearch.WordTrace]
  refine ⟨950413339600053774644101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1267217786133405032858801 950413339600053774644101)
  ·
    refine ⟨178202501175010082745769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 950413339600053774644101 178202501175010082745769)
    ·
      refine ⟨133651875881257562059327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178202501175010082745769 133651875881257562059327)
      ·
        refine ⟨200477813821886343088991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133651875881257562059327 200477813821886343088991)
        ·
          refine ⟨300716720732829514633487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200477813821886343088991 300716720732829514633487)
          ·
            refine ⟨451075081099244271950231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300716720732829514633487 451075081099244271950231)
            ·
              refine ⟨676612621648866407925347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 451075081099244271950231 676612621648866407925347)
              ·
                refine ⟨1014918932473299611888021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 676612621648866407925347 1014918932473299611888021)
                ·
                  refine ⟨47574324959685919307251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1014918932473299611888021 47574324959685919307251)
                  ·
                    refine ⟨71361487439528878960877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47574324959685919307251 71361487439528878960877)
                    ·
                      refine ⟨26760557789823329610329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 71361487439528878960877 26760557789823329610329)
                      ·
                        rfl

theorem cell23_52116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_52116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_52116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_52116 prefixEnd_52116 := by exact prefixLift 52116
  have htrace : WordTrace (prefixWord ++ tailWord_52116) baseStart_52116 baseEnd_52116 := by
    simpa [prefixWord, tailWord_52116, baseEnd_52116] using wordTrace_append hprefix tailTrace_52116
  have hstable : (prefixWord ++ tailWord_52116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52116).length < 2 ^ (prefixWord ++ tailWord_52116).sum := by decide
  have hdescent : baseEnd_52116 < baseStart_52116 := by decide
  rcases family_descends (prefixWord ++ tailWord_52116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52139 : List Nat := [1, 1, 1, 1, 2, 1, 1, 6, 3, 4, 2]
def baseStart_52139 : Nat := 118140960795 + 52139 * 2 ^ 59
def prefixEnd_52139 : Nat := 4983230072969 + 3 ^ 40 * 52139 * 2
def baseEnd_52139 : Nat := 26772367844876739622723

theorem tailTrace_52139 : CollatzResearch.WordTrace tailWord_52139 prefixEnd_52139 26772367844876739622723 := by
  unfold tailWord_52139
  simp only [CollatzResearch.WordTrace]
  refine ⟨1901665558116782477375471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1267777038744521651583647 1901665558116782477375471)
  ·
    refine ⟨2852498337175173716063207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1901665558116782477375471 2852498337175173716063207)
    ·
      refine ⟨4278747505762760574094811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2852498337175173716063207 4278747505762760574094811)
      ·
        refine ⟨6418121258644140861142217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4278747505762760574094811 6418121258644140861142217)
        ·
          refine ⟨4813590943983105645856663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6418121258644140861142217 4813590943983105645856663)
          ·
            refine ⟨7220386415974658468784995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4813590943983105645856663 7220386415974658468784995)
            ·
              refine ⟨10830579623961987703177493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7220386415974658468784995 10830579623961987703177493)
              ·
                refine ⟨507683419873218173586445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10830579623961987703177493 507683419873218173586445)
                ·
                  refine ⟨190381282452456815094917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 507683419873218173586445 190381282452456815094917)
                  ·
                    refine ⟨35696490459835652830297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 190381282452456815094917 35696490459835652830297)
                    ·
                      refine ⟨26772367844876739622723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 35696490459835652830297 26772367844876739622723)
                      ·
                        rfl

theorem cell23_52139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 3, 4, 2].length) (baseStart_52139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_52139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_52139 prefixEnd_52139 := by exact prefixLift 52139
  have htrace : WordTrace (prefixWord ++ tailWord_52139) baseStart_52139 baseEnd_52139 := by
    simpa [prefixWord, tailWord_52139, baseEnd_52139] using wordTrace_append hprefix tailTrace_52139
  have hstable : (prefixWord ++ tailWord_52139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52139).length < 2 ^ (prefixWord ++ tailWord_52139).sum := by decide
  have hdescent : baseEnd_52139 < baseStart_52139 := by decide
  rcases family_descends (prefixWord ++ tailWord_52139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52192 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 5, 7]
def baseStart_52192 : Nat := 118140960795 + 52192 * 2 ^ 59
def prefixEnd_52192 : Nat := 4983230072969 + 3 ^ 40 * 52192 * 2
def baseEnd_52192 : Nat := 8933194106521677419993

theorem tailTrace_52192 : CollatzResearch.WordTrace tailWord_52192 prefixEnd_52192 8933194106521677419993 := by
  unfold tailWord_52192
  simp only [CollatzResearch.WordTrace]
  refine ⟨951799313462386264527415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1269065751283181686036553 951799313462386264527415)
  ·
    refine ⟨1427698970193579396791123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 951799313462386264527415 1427698970193579396791123)
    ·
      refine ⟨2141548455290369095186685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1427698970193579396791123 2141548455290369095186685)
      ·
        refine ⟨803080670733888410695007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2141548455290369095186685 803080670733888410695007)
        ·
          refine ⟨1204621006100832616042511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 803080670733888410695007 1204621006100832616042511)
          ·
            refine ⟨1806931509151248924063767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1204621006100832616042511 1806931509151248924063767)
            ·
              refine ⟨2710397263726873386095651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1806931509151248924063767 2710397263726873386095651)
              ·
                refine ⟨4065595895590310079143477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2710397263726873386095651 4065595895590310079143477)
                ·
                  refine ⟨381149615211591569919701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4065595895590310079143477 381149615211591569919701)
                  ·
                    refine ⟨8933194106521677419993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 381149615211591569919701 8933194106521677419993)
                    ·
                      rfl

theorem cell23_52192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 5, 7].length) (baseStart_52192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_52192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_52192 prefixEnd_52192 := by exact prefixLift 52192
  have htrace : WordTrace (prefixWord ++ tailWord_52192) baseStart_52192 baseEnd_52192 := by
    simpa [prefixWord, tailWord_52192, baseEnd_52192] using wordTrace_append hprefix tailTrace_52192
  have hstable : (prefixWord ++ tailWord_52192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52192).length < 2 ^ (prefixWord ++ tailWord_52192).sum := by decide
  have hdescent : baseEnd_52192 < baseStart_52192 := by decide
  rcases family_descends (prefixWord ++ tailWord_52192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52213 : List Nat := [1, 3, 5, 2, 1, 1, 1, 2, 7]
def baseStart_52213 : Nat := 118140960795 + 52213 * 2 ^ 59
def prefixEnd_52213 : Nat := 4983230072969 + 3 ^ 40 * 52213 * 2
def baseEnd_52213 : Nat := 2978929490367716677487

theorem tailTrace_52213 : CollatzResearch.WordTrace tailWord_52213 prefixEnd_52213 2978929490367716677487 := by
  unfold tailWord_52213
  simp only [CollatzResearch.WordTrace]
  refine ⟨1904364559848693115569293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1269576373232462077046195 1904364559848693115569293)
  ·
    refine ⟨714136709943259918338485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1904364559848693115569293 714136709943259918338485)
    ·
      refine ⟨66950316557180617344233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 714136709943259918338485 66950316557180617344233)
      ·
        refine ⟨50212737417885463008175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66950316557180617344233 50212737417885463008175)
        ·
          refine ⟨75319106126828194512263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50212737417885463008175 75319106126828194512263)
          ·
            refine ⟨112978659190242291768395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75319106126828194512263 112978659190242291768395)
            ·
              refine ⟨169467988785363437652593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112978659190242291768395 169467988785363437652593)
              ·
                refine ⟨127100991589022578239445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169467988785363437652593 127100991589022578239445)
                ·
                  refine ⟨2978929490367716677487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 127100991589022578239445 2978929490367716677487)
                  ·
                    rfl

theorem cell23_52213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 2, 7].length) (baseStart_52213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_52213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_52213 prefixEnd_52213 := by exact prefixLift 52213
  have htrace : WordTrace (prefixWord ++ tailWord_52213) baseStart_52213 baseEnd_52213 := by
    simpa [prefixWord, tailWord_52213, baseEnd_52213] using wordTrace_append hprefix tailTrace_52213
  have hstable : (prefixWord ++ tailWord_52213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52213).length < 2 ^ (prefixWord ++ tailWord_52213).sum := by decide
  have hdescent : baseEnd_52213 < baseStart_52213 := by decide
  rcases family_descends (prefixWord ++ tailWord_52213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52229 : List Nat := [1, 3, 1, 1, 2, 3, 3, 1, 1, 3, 4]
def baseStart_52229 : Nat := 118140960795 + 52229 * 2 ^ 59
def prefixEnd_52229 : Nat := 4983230072969 + 3 ^ 40 * 52229 * 2
def baseEnd_52229 : Nat := 26818581103781387497309

theorem tailTrace_52229 : CollatzResearch.WordTrace tailWord_52229 prefixEnd_52229 26818581103781387497309 := by
  unfold tailWord_52229
  simp only [CollatzResearch.WordTrace]
  refine ⟨1904948127790727848151741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1269965418527151898767827 1904948127790727848151741)
  ·
    refine ⟨714355547921522943056903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1904948127790727848151741 714355547921522943056903)
    ·
      refine ⟨1071533321882284414585355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 714355547921522943056903 1071533321882284414585355)
      ·
        refine ⟨1607299982823426621878033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1071533321882284414585355 1607299982823426621878033)
        ·
          refine ⟨1205474987117569966408525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1607299982823426621878033 1205474987117569966408525)
          ·
            refine ⟨452053120169088737403197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1205474987117569966408525 452053120169088737403197)
            ·
              refine ⟨169519920063408276526199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 452053120169088737403197 169519920063408276526199)
              ·
                refine ⟨254279880095112414789299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169519920063408276526199 254279880095112414789299)
                ·
                  refine ⟨381419820142668622183949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 254279880095112414789299 381419820142668622183949)
                  ·
                    refine ⟨143032432553500733318981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 381419820142668622183949 143032432553500733318981)
                    ·
                      refine ⟨26818581103781387497309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 143032432553500733318981 26818581103781387497309)
                      ·
                        rfl

theorem cell23_52229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 3, 4].length) (baseStart_52229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_52229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_52229 prefixEnd_52229 := by exact prefixLift 52229
  have htrace : WordTrace (prefixWord ++ tailWord_52229) baseStart_52229 baseEnd_52229 := by
    simpa [prefixWord, tailWord_52229, baseEnd_52229] using wordTrace_append hprefix tailTrace_52229
  have hstable : (prefixWord ++ tailWord_52229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52229).length < 2 ^ (prefixWord ++ tailWord_52229).sum := by decide
  have hdescent : baseEnd_52229 < baseStart_52229 := by decide
  rcases family_descends (prefixWord ++ tailWord_52229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52279 : List Nat := [1, 1, 3, 1, 2, 2, 1, 1, 1, 7, 3]
def baseStart_52279 : Nat := 118140960795 + 52279 * 2 ^ 59
def prefixEnd_52279 : Nat := 4983230072969 + 3 ^ 40 * 52279 * 2
def baseEnd_52279 : Nat := 26844255136506191872079

theorem tailTrace_52279 : CollatzResearch.WordTrace tailWord_52279 prefixEnd_52279 26844255136506191872079 := by
  unfold tailWord_52279
  simp only [CollatzResearch.WordTrace]
  refine ⟨1906771777609586387471891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1271181185073057591647927 1906771777609586387471891)
  ·
    refine ⟨2860157666414379581207837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1906771777609586387471891 2860157666414379581207837)
    ·
      refine ⟨1072559124905392342952939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2860157666414379581207837 1072559124905392342952939)
      ·
        refine ⟨1608838687358088514429409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1072559124905392342952939 1608838687358088514429409)
        ·
          refine ⟨1206629015518566385822057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1608838687358088514429409 1206629015518566385822057)
          ·
            refine ⟨904971761638924789366543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1206629015518566385822057 904971761638924789366543)
            ·
              refine ⟨1357457642458387184049815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 904971761638924789366543 1357457642458387184049815)
              ·
                refine ⟨2036186463687580776074723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1357457642458387184049815 2036186463687580776074723)
                ·
                  refine ⟨3054279695531371164112085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2036186463687580776074723 3054279695531371164112085)
                  ·
                    refine ⟨71584680364016511658877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3054279695531371164112085 71584680364016511658877)
                    ·
                      refine ⟨26844255136506191872079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 71584680364016511658877 26844255136506191872079)
                      ·
                        rfl

theorem cell23_52279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 7, 3].length) (baseStart_52279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_52279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_52279 prefixEnd_52279 := by exact prefixLift 52279
  have htrace : WordTrace (prefixWord ++ tailWord_52279) baseStart_52279 baseEnd_52279 := by
    simpa [prefixWord, tailWord_52279, baseEnd_52279] using wordTrace_append hprefix tailTrace_52279
  have hstable : (prefixWord ++ tailWord_52279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52279).length < 2 ^ (prefixWord ++ tailWord_52279).sum := by decide
  have hdescent : baseEnd_52279 < baseStart_52279 := by decide
  rcases family_descends (prefixWord ++ tailWord_52279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52286 : List Nat := [4, 2, 1, 3, 1, 1, 1, 2, 8]
def baseStart_52286 : Nat := 118140960795 + 52286 * 2 ^ 59
def prefixEnd_52286 : Nat := 4983230072969 + 3 ^ 40 * 52286 * 2
def baseEnd_52286 : Nat := 2983094389009740498283

theorem tailTrace_52286 : CollatzResearch.WordTrace tailWord_52286 prefixEnd_52286 2983094389009740498283 := by
  unfold tailWord_52286
  simp only [CollatzResearch.WordTrace]
  refine ⟨238378386073028322872089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1271351392389484388651141 238378386073028322872089)
  ·
    refine ⟨178783789554771242154067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238378386073028322872089 178783789554771242154067)
    ·
      refine ⟨268175684332156863231101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178783789554771242154067 268175684332156863231101)
      ·
        refine ⟨100565881624558823711663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 268175684332156863231101 100565881624558823711663)
        ·
          refine ⟨150848822436838235567495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100565881624558823711663 150848822436838235567495)
          ·
            refine ⟨226273233655257353351243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150848822436838235567495 226273233655257353351243)
            ·
              refine ⟨339409850482886030026865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226273233655257353351243 339409850482886030026865)
              ·
                refine ⟨254557387862164522520149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 339409850482886030026865 254557387862164522520149)
                ·
                  refine ⟨2983094389009740498283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 254557387862164522520149 2983094389009740498283)
                  ·
                    rfl

theorem cell23_52286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 8].length) (baseStart_52286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_52286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_52286 prefixEnd_52286 := by exact prefixLift 52286
  have htrace : WordTrace (prefixWord ++ tailWord_52286) baseStart_52286 baseEnd_52286 := by
    simpa [prefixWord, tailWord_52286, baseEnd_52286] using wordTrace_append hprefix tailTrace_52286
  have hstable : (prefixWord ++ tailWord_52286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52286).length < 2 ^ (prefixWord ++ tailWord_52286).sum := by decide
  have hdescent : baseEnd_52286 < baseStart_52286 := by decide
  rcases family_descends (prefixWord ++ tailWord_52286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52316 : List Nat := [2, 2, 4, 1, 1, 1, 2, 2, 3, 5]
def baseStart_52316 : Nat := 118140960795 + 52316 * 2 ^ 59
def prefixEnd_52316 : Nat := 4983230072969 + 3 ^ 40 * 52316 * 2
def baseEnd_52316 : Nat := 8954417973574182369803

theorem tailTrace_52316 : CollatzResearch.WordTrace tailWord_52316 prefixEnd_52316 8954417973574182369803 := by
  unfold tailWord_52316
  simp only [CollatzResearch.WordTrace]
  refine ⟨954060639237770853284401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1272080852317027804379201 954060639237770853284401)
  ·
    refine ⟨715545479428328139963301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 954060639237770853284401 715545479428328139963301)
    ·
      refine ⟨134164777392811526243119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 715545479428328139963301 134164777392811526243119)
      ·
        refine ⟨201247166089217289364679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134164777392811526243119 201247166089217289364679)
        ·
          refine ⟨301870749133825934047019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201247166089217289364679 301870749133825934047019)
          ·
            refine ⟨452806123700738901070529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301870749133825934047019 452806123700738901070529)
            ·
              refine ⟨339604592775554175802897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 452806123700738901070529 339604592775554175802897)
              ·
                refine ⟨254703444581665631852173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 339604592775554175802897 254703444581665631852173)
                ·
                  refine ⟨95513791718124611944565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 254703444581665631852173 95513791718124611944565)
                  ·
                    refine ⟨8954417973574182369803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 95513791718124611944565 8954417973574182369803)
                    ·
                      rfl

theorem cell23_52316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_52316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_52316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_52316 prefixEnd_52316 := by exact prefixLift 52316
  have htrace : WordTrace (prefixWord ++ tailWord_52316) baseStart_52316 baseEnd_52316 := by
    simpa [prefixWord, tailWord_52316, baseEnd_52316] using wordTrace_append hprefix tailTrace_52316
  have hstable : (prefixWord ++ tailWord_52316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52316).length < 2 ^ (prefixWord ++ tailWord_52316).sum := by decide
  have hdescent : baseEnd_52316 < baseStart_52316 := by decide
  rcases family_descends (prefixWord ++ tailWord_52316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52333 : List Nat := [1, 5, 1, 1, 2, 2, 3, 2, 1, 5]
def baseStart_52333 : Nat := 118140960795 + 52333 * 2 ^ 59
def prefixEnd_52333 : Nat := 4983230072969 + 3 ^ 40 * 52333 * 2
def baseEnd_52333 : Nat := 8957327697282993532277

theorem tailTrace_52333 : CollatzResearch.WordTrace tailWord_52333 prefixEnd_52333 8957327697282993532277 := by
  unfold tailWord_52333
  simp only [CollatzResearch.WordTrace]
  refine ⟨1908741319413953609937653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1272494212942635739958435 1908741319413953609937653)
  ·
    refine ⟨178944498695058150931655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1908741319413953609937653 178944498695058150931655)
    ·
      refine ⟨268416748042587226397483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178944498695058150931655 268416748042587226397483)
      ·
        refine ⟨402625122063880839596225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268416748042587226397483 402625122063880839596225)
        ·
          refine ⟨301968841547910629697169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 402625122063880839596225 301968841547910629697169)
          ·
            refine ⟨226476631160932972272877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 301968841547910629697169 226476631160932972272877)
            ·
              refine ⟨84928736685349864602329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 226476631160932972272877 84928736685349864602329)
              ·
                refine ⟨63696552514012398451747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84928736685349864602329 63696552514012398451747)
                ·
                  refine ⟨95544828771018597677621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63696552514012398451747 95544828771018597677621)
                  ·
                    refine ⟨8957327697282993532277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 95544828771018597677621 8957327697282993532277)
                    ·
                      rfl

theorem cell23_52333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_52333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_52333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_52333 prefixEnd_52333 := by exact prefixLift 52333
  have htrace : WordTrace (prefixWord ++ tailWord_52333) baseStart_52333 baseEnd_52333 := by
    simpa [prefixWord, tailWord_52333, baseEnd_52333] using wordTrace_append hprefix tailTrace_52333
  have hstable : (prefixWord ++ tailWord_52333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52333).length < 2 ^ (prefixWord ++ tailWord_52333).sum := by decide
  have hdescent : baseEnd_52333 < baseStart_52333 := by decide
  rcases family_descends (prefixWord ++ tailWord_52333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52336 : List Nat := [2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 4]
def baseStart_52336 : Nat := 118140960795 + 52336 * 2 ^ 59
def prefixEnd_52336 : Nat := 4983230072969 + 3 ^ 40 * 52336 * 2
def baseEnd_52336 : Nat := 26873523533812468859317

theorem tailTrace_52336 : CollatzResearch.WordTrace tailWord_52336 prefixEnd_52336 26873523533812468859317 := by
  unfold tailWord_52336
  simp only [CollatzResearch.WordTrace]
  refine ⟨954425369201542561148431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1272567158935390081531241 954425369201542561148431)
  ·
    refine ⟨1431638053802313841722647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 954425369201542561148431 1431638053802313841722647)
    ·
      refine ⟨2147457080703470762583971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1431638053802313841722647 2147457080703470762583971)
      ·
        refine ⟨3221185621055206143875957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2147457080703470762583971 3221185621055206143875957)
        ·
          refine ⟨301986151973925575988371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3221185621055206143875957 301986151973925575988371)
          ·
            refine ⟨452979227960888363982557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301986151973925575988371 452979227960888363982557)
            ·
              refine ⟨169867210485333136493459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 452979227960888363982557 169867210485333136493459)
              ·
                refine ⟨254800815727999704740189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169867210485333136493459 254800815727999704740189)
                ·
                  refine ⟨95550305897999889277571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 254800815727999704740189 95550305897999889277571)
                  ·
                    refine ⟨143325458846999833916357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 95550305897999889277571 143325458846999833916357)
                    ·
                      refine ⟨26873523533812468859317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 143325458846999833916357 26873523533812468859317)
                      ·
                        rfl

theorem cell23_52336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 4].length) (baseStart_52336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_52336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_52336 prefixEnd_52336 := by exact prefixLift 52336
  have htrace : WordTrace (prefixWord ++ tailWord_52336) baseStart_52336 baseEnd_52336 := by
    simpa [prefixWord, tailWord_52336, baseEnd_52336] using wordTrace_append hprefix tailTrace_52336
  have hstable : (prefixWord ++ tailWord_52336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52336).length < 2 ^ (prefixWord ++ tailWord_52336).sum := by decide
  have hdescent : baseEnd_52336 < baseStart_52336 := by decide
  rcases family_descends (prefixWord ++ tailWord_52336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52376 : List Nat := [2, 1, 2, 4, 2, 1, 3, 8]
def baseStart_52376 : Nat := 118140960795 + 52376 * 2 ^ 59
def prefixEnd_52376 : Nat := 4983230072969 + 3 ^ 40 * 52376 * 2
def baseEnd_52376 : Nat := 996076398518233791079

theorem tailTrace_52376 : CollatzResearch.WordTrace tailWord_52376 prefixEnd_52376 996076398518233791079 := by
  unfold tailWord_52376
  simp only [CollatzResearch.WordTrace]
  refine ⟨955154829129085976876491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1273539772172114635835321 955154829129085976876491)
  ·
    refine ⟨1432732243693628965314737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 955154829129085976876491 1432732243693628965314737)
    ·
      refine ⟨1074549182770221723986053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1432732243693628965314737 1074549182770221723986053)
      ·
        refine ⟨201477971769416573247385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1074549182770221723986053 201477971769416573247385)
        ·
          refine ⟨151108478827062429935539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201477971769416573247385 151108478827062429935539)
          ·
            refine ⟨226662718240593644903309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151108478827062429935539 226662718240593644903309)
            ·
              refine ⟨84998519340222616838741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 226662718240593644903309 84998519340222616838741)
              ·
                refine ⟨996076398518233791079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 84998519340222616838741 996076398518233791079)
                ·
                  rfl

theorem cell23_52376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 8].length) (baseStart_52376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_52376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_52376 prefixEnd_52376 := by exact prefixLift 52376
  have htrace : WordTrace (prefixWord ++ tailWord_52376) baseStart_52376 baseEnd_52376 := by
    simpa [prefixWord, tailWord_52376, baseEnd_52376] using wordTrace_append hprefix tailTrace_52376
  have hstable : (prefixWord ++ tailWord_52376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52376).length < 2 ^ (prefixWord ++ tailWord_52376).sum := by decide
  have hdescent : baseEnd_52376 < baseStart_52376 := by decide
  rcases family_descends (prefixWord ++ tailWord_52376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52460 : List Nat := [2, 2, 1, 1, 2, 4, 1, 2, 4, 2, 2]
def baseStart_52460 : Nat := 118140960795 + 52460 * 2 ^ 59
def prefixEnd_52460 : Nat := 4983230072969 + 3 ^ 40 * 52460 * 2
def baseEnd_52460 : Nat := 26937195134969983708747

theorem tailTrace_52460 : CollatzResearch.WordTrace tailWord_52460 prefixEnd_52460 26937195134969983708747 := by
  unfold tailWord_52460
  simp only [CollatzResearch.WordTrace]
  refine ⟨956686694976927149905417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1275582259969236199873889 956686694976927149905417)
  ·
    refine ⟨717515021232695362429063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 956686694976927149905417 717515021232695362429063)
    ·
      refine ⟨1076272531849043043643595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 717515021232695362429063 1076272531849043043643595)
      ·
        refine ⟨1614408797773564565465393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1076272531849043043643595 1614408797773564565465393)
        ·
          refine ⟨1210806598330173424099045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1614408797773564565465393 1210806598330173424099045)
          ·
            refine ⟨227026237186907517018571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1210806598330173424099045 227026237186907517018571)
            ·
              refine ⟨340539355780361275527857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 227026237186907517018571 340539355780361275527857)
              ·
                refine ⟨255404516835270956645893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 340539355780361275527857 255404516835270956645893)
                ·
                  refine ⟨47888346906613304371105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 255404516835270956645893 47888346906613304371105)
                  ·
                    refine ⟨35916260179959978278329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47888346906613304371105 35916260179959978278329)
                    ·
                      refine ⟨26937195134969983708747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 35916260179959978278329 26937195134969983708747)
                      ·
                        rfl

theorem cell23_52460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 2, 2].length) (baseStart_52460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_52460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_52460 prefixEnd_52460 := by exact prefixLift 52460
  have htrace : WordTrace (prefixWord ++ tailWord_52460) baseStart_52460 baseEnd_52460 := by
    simpa [prefixWord, tailWord_52460, baseEnd_52460] using wordTrace_append hprefix tailTrace_52460
  have hstable : (prefixWord ++ tailWord_52460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52460).length < 2 ^ (prefixWord ++ tailWord_52460).sum := by decide
  have hdescent : baseEnd_52460 < baseStart_52460 := by decide
  rcases family_descends (prefixWord ++ tailWord_52460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52463 : List Nat := [1, 1, 2, 1, 7, 1, 1, 1, 2, 1, 5]
def baseStart_52463 : Nat := 118140960795 + 52463 * 2 ^ 59
def prefixEnd_52463 : Nat := 4983230072969 + 3 ^ 40 * 52463 * 2
def baseEnd_52463 : Nat := 26938735576933471971233

theorem tailTrace_52463 : CollatzResearch.WordTrace tailWord_52463 prefixEnd_52463 26938735576933471971233 := by
  unfold tailWord_52463
  simp only [CollatzResearch.WordTrace]
  refine ⟨1913482808942985812170043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1275655205961990541446695 1913482808942985812170043)
  ·
    refine ⟨2870224213414478718255065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1913482808942985812170043 2870224213414478718255065)
    ·
      refine ⟨2152668160060859038691299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2870224213414478718255065 2152668160060859038691299)
      ·
        refine ⟨3229002240091288558036949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2152668160060859038691299 3229002240091288558036949)
        ·
          refine ⟨75679740002139575578991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 3229002240091288558036949 75679740002139575578991)
          ·
            refine ⟨113519610003209363368487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75679740002139575578991 113519610003209363368487)
            ·
              refine ⟨170279415004814045052731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113519610003209363368487 170279415004814045052731)
              ·
                refine ⟨255419122507221067579097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170279415004814045052731 255419122507221067579097)
                ·
                  refine ⟨191564341880415800684323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 255419122507221067579097 191564341880415800684323)
                  ·
                    refine ⟨287346512820623701026485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 191564341880415800684323 287346512820623701026485)
                    ·
                      refine ⟨26938735576933471971233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 287346512820623701026485 26938735576933471971233)
                      ·
                        rfl

theorem cell23_52463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 2, 1, 5].length) (baseStart_52463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_52463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_52463 prefixEnd_52463 := by exact prefixLift 52463
  have htrace : WordTrace (prefixWord ++ tailWord_52463) baseStart_52463 baseEnd_52463 := by
    simpa [prefixWord, tailWord_52463, baseEnd_52463] using wordTrace_append hprefix tailTrace_52463
  have hstable : (prefixWord ++ tailWord_52463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52463).length < 2 ^ (prefixWord ++ tailWord_52463).sum := by decide
  have hdescent : baseEnd_52463 < baseStart_52463 := by decide
  rcases family_descends (prefixWord ++ tailWord_52463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52483 : List Nat := [1, 1, 1, 3, 2, 6, 1, 1, 7]
def baseStart_52483 : Nat := 118140960795 + 52483 * 2 ^ 59
def prefixEnd_52483 : Nat := 4983230072969 + 3 ^ 40 * 52483 * 2
def baseEnd_52483 : Nat := 2994333910002599302349

theorem tailTrace_52483 : CollatzResearch.WordTrace tailWord_52483 prefixEnd_52483 2994333910002599302349 := by
  unfold tailWord_52483
  simp only [CollatzResearch.WordTrace]
  refine ⟨1914212268870529227898103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1276141512580352818598735 1914212268870529227898103)
  ·
    refine ⟨2871318403305793841847155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1914212268870529227898103 2871318403305793841847155)
    ·
      refine ⟨4306977604958690762770733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2871318403305793841847155 4306977604958690762770733)
      ·
        refine ⟨1615116601859509036039025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4306977604958690762770733 1615116601859509036039025)
        ·
          refine ⟨1211337451394631777029269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1615116601859509036039025 1211337451394631777029269)
          ·
            refine ⟨56781443034123364548247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1211337451394631777029269 56781443034123364548247)
            ·
              refine ⟨85172164551185046822371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56781443034123364548247 85172164551185046822371)
              ·
                refine ⟨127758246826777570233557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85172164551185046822371 127758246826777570233557)
                ·
                  refine ⟨2994333910002599302349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 127758246826777570233557 2994333910002599302349)
                  ·
                    rfl

theorem cell23_52483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 1, 7].length) (baseStart_52483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_52483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_52483 prefixEnd_52483 := by exact prefixLift 52483
  have htrace : WordTrace (prefixWord ++ tailWord_52483) baseStart_52483 baseEnd_52483 := by
    simpa [prefixWord, tailWord_52483, baseEnd_52483] using wordTrace_append hprefix tailTrace_52483
  have hstable : (prefixWord ++ tailWord_52483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52483).length < 2 ^ (prefixWord ++ tailWord_52483).sum := by decide
  have hdescent : baseEnd_52483 < baseStart_52483 := by decide
  rcases family_descends (prefixWord ++ tailWord_52483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52494 : List Nat := [4, 1, 1, 2, 1, 3, 4, 1, 2, 2, 2]
def baseStart_52494 : Nat := 118140960795 + 52494 * 2 ^ 59
def prefixEnd_52494 : Nat := 4983230072969 + 3 ^ 40 * 52494 * 2
def baseEnd_52494 : Nat := 26954653477222850683591

theorem tailTrace_52494 : CollatzResearch.WordTrace tailWord_52494 prefixEnd_52494 26954653477222850683591 := by
  unfold tailWord_52494
  simp only [CollatzResearch.WordTrace]
  refine ⟨239326683978834763318567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1276408981220452071032357 239326683978834763318567)
  ·
    refine ⟨358990025968252144977851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239326683978834763318567 358990025968252144977851)
    ·
      refine ⟨538485038952378217466777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358990025968252144977851 538485038952378217466777)
      ·
        refine ⟨403863779214283663100083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 538485038952378217466777 403863779214283663100083)
        ·
          refine ⟨605795668821425494650125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 403863779214283663100083 605795668821425494650125)
          ·
            refine ⟨227173375808034560493797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 605795668821425494650125 227173375808034560493797)
            ·
              refine ⟨42595007964006480092587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 227173375808034560493797 42595007964006480092587)
              ·
                refine ⟨63892511946009720138881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42595007964006480092587 63892511946009720138881)
                ·
                  refine ⟨47919383959507290104161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63892511946009720138881 47919383959507290104161)
                  ·
                    refine ⟨35939537969630467578121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47919383959507290104161 35939537969630467578121)
                    ·
                      refine ⟨26954653477222850683591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 35939537969630467578121 26954653477222850683591)
                      ·
                        rfl

theorem cell23_52494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 4, 1, 2, 2, 2].length) (baseStart_52494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_52494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_52494 prefixEnd_52494 := by exact prefixLift 52494
  have htrace : WordTrace (prefixWord ++ tailWord_52494) baseStart_52494 baseEnd_52494 := by
    simpa [prefixWord, tailWord_52494, baseEnd_52494] using wordTrace_append hprefix tailTrace_52494
  have hstable : (prefixWord ++ tailWord_52494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52494).length < 2 ^ (prefixWord ++ tailWord_52494).sum := by decide
  have hdescent : baseEnd_52494 < baseStart_52494 := by decide
  rcases family_descends (prefixWord ++ tailWord_52494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52498 : List Nat := [3, 2, 4, 2, 2, 1, 1, 2, 1, 3, 2]
def baseStart_52498 : Nat := 118140960795 + 52498 * 2 ^ 59
def prefixEnd_52498 : Nat := 4983230072969 + 3 ^ 40 * 52498 * 2
def baseEnd_52498 : Nat := 26956707399840835033573

theorem tailTrace_52498 : CollatzResearch.WordTrace tailWord_52498 prefixEnd_52498 26956707399840835033573 := by
  unfold tailWord_52498
  simp only [CollatzResearch.WordTrace]
  refine ⟨478689840954046697423537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1276506242544124526462765 478689840954046697423537)
  ·
    refine ⟨359017380715535023067653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 478689840954046697423537 359017380715535023067653)
    ·
      refine ⟨67315758884162816825185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 359017380715535023067653 67315758884162816825185)
      ·
        refine ⟨50486819163122112618889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67315758884162816825185 50486819163122112618889)
        ·
          refine ⟨37865114372341584464167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50486819163122112618889 37865114372341584464167)
          ·
            refine ⟨56797671558512376696251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37865114372341584464167 56797671558512376696251)
            ·
              refine ⟨85196507337768565044377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56797671558512376696251 85196507337768565044377)
              ·
                refine ⟨63897380503326423783283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85196507337768565044377 63897380503326423783283)
                ·
                  refine ⟨95846070754989635674925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63897380503326423783283 95846070754989635674925)
                  ·
                    refine ⟨35942276533121113378097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 95846070754989635674925 35942276533121113378097)
                    ·
                      refine ⟨26956707399840835033573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 35942276533121113378097 26956707399840835033573)
                      ·
                        rfl

theorem cell23_52498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_52498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_52498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_52498 prefixEnd_52498 := by exact prefixLift 52498
  have htrace : WordTrace (prefixWord ++ tailWord_52498) baseStart_52498 baseEnd_52498 := by
    simpa [prefixWord, tailWord_52498, baseEnd_52498] using wordTrace_append hprefix tailTrace_52498
  have hstable : (prefixWord ++ tailWord_52498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52498).length < 2 ^ (prefixWord ++ tailWord_52498).sum := by decide
  have hdescent : baseEnd_52498 < baseStart_52498 := by decide
  rcases family_descends (prefixWord ++ tailWord_52498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52534 : List Nat := [5, 1, 2, 3, 1, 1, 1, 4, 5]
def baseStart_52534 : Nat := 118140960795 + 52534 * 2 ^ 59
def prefixEnd_52534 : Nat := 4983230072969 + 3 ^ 40 * 52534 * 2
def baseEnd_52534 : Nat := 2997243633711410464823

theorem tailTrace_52534 : CollatzResearch.WordTrace tailWord_52534 prefixEnd_52534 2997243633711410464823 := by
  unfold tailWord_52534
  simp only [CollatzResearch.WordTrace]
  refine ⟨119754524480360308625291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1277381594457176625336437 119754524480360308625291)
  ·
    refine ⟨179631786720540462937937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119754524480360308625291 179631786720540462937937)
    ·
      refine ⟨134723840040405347203453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179631786720540462937937 134723840040405347203453)
      ·
        refine ⟨50521440015152005201295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134723840040405347203453 50521440015152005201295)
        ·
          refine ⟨75782160022728007801943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50521440015152005201295 75782160022728007801943)
          ·
            refine ⟨113673240034092011702915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75782160022728007801943 113673240034092011702915)
            ·
              refine ⟨170509860051138017554373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113673240034092011702915 170509860051138017554373)
              ·
                refine ⟨31970598759588378291445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 170509860051138017554373 31970598759588378291445)
                ·
                  refine ⟨2997243633711410464823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31970598759588378291445 2997243633711410464823)
                  ·
                    rfl

theorem cell23_52534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 4, 5].length) (baseStart_52534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_52534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_52534 prefixEnd_52534 := by exact prefixLift 52534
  have htrace : WordTrace (prefixWord ++ tailWord_52534) baseStart_52534 baseEnd_52534 := by
    simpa [prefixWord, tailWord_52534, baseEnd_52534] using wordTrace_append hprefix tailTrace_52534
  have hstable : (prefixWord ++ tailWord_52534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52534).length < 2 ^ (prefixWord ++ tailWord_52534).sum := by decide
  have hdescent : baseEnd_52534 < baseStart_52534 := by decide
  rcases family_descends (prefixWord ++ tailWord_52534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52536 : List Nat := [2, 1, 2, 1, 3, 1, 1, 1, 1, 5, 5]
def baseStart_52536 : Nat := 118140960795 + 52536 * 2 ^ 59
def prefixEnd_52536 : Nat := 4983230072969 + 3 ^ 40 * 52536 * 2
def baseEnd_52536 : Nat := 26976219664711686358397

theorem tailTrace_52536 : CollatzResearch.WordTrace tailWord_52536 prefixEnd_52536 26976219664711686358397 := by
  unfold tailWord_52536
  simp only [CollatzResearch.WordTrace]
  refine ⟨958072668839259639788731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1277430225119012853051641 958072668839259639788731)
  ·
    refine ⟨1437109003258889459683097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 958072668839259639788731 1437109003258889459683097)
    ·
      refine ⟨1077831752444167094762323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1437109003258889459683097 1077831752444167094762323)
      ·
        refine ⟨1616747628666250642143485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1077831752444167094762323 1616747628666250642143485)
        ·
          refine ⟨606280360749843990803807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1616747628666250642143485 606280360749843990803807)
          ·
            refine ⟨909420541124765986205711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 606280360749843990803807 909420541124765986205711)
            ·
              refine ⟨1364130811687148979308567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 909420541124765986205711 1364130811687148979308567)
              ·
                refine ⟨2046196217530723468962851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1364130811687148979308567 2046196217530723468962851)
                ·
                  refine ⟨3069294326296085203444277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2046196217530723468962851 3069294326296085203444277)
                  ·
                    refine ⟨287746343090257987822901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3069294326296085203444277 287746343090257987822901)
                    ·
                      refine ⟨26976219664711686358397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 287746343090257987822901 26976219664711686358397)
                      ·
                        rfl

theorem cell23_52536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 1, 5, 5].length) (baseStart_52536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_52536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_52536 prefixEnd_52536 := by exact prefixLift 52536
  have htrace : WordTrace (prefixWord ++ tailWord_52536) baseStart_52536 baseEnd_52536 := by
    simpa [prefixWord, tailWord_52536, baseEnd_52536] using wordTrace_append hprefix tailTrace_52536
  have hstable : (prefixWord ++ tailWord_52536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52536).length < 2 ^ (prefixWord ++ tailWord_52536).sum := by decide
  have hdescent : baseEnd_52536 < baseStart_52536 := by decide
  rcases family_descends (prefixWord ++ tailWord_52536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52553 : List Nat := [1, 2, 1, 1, 2, 3, 2, 2, 4, 2, 3]
def baseStart_52553 : Nat := 118140960795 + 52553 * 2 ^ 59
def prefixEnd_52553 : Nat := 4983230072969 + 3 ^ 40 * 52553 * 2
def baseEnd_52553 : Nat := 26984948835838119845819

theorem tailTrace_52553 : CollatzResearch.WordTrace tailWord_52553 prefixEnd_52553 26984948835838119845819 := by
  unfold tailWord_52553
  simp only [CollatzResearch.WordTrace]
  refine ⟨1916765378616931182946313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1277843585744620788630875 1916765378616931182946313)
  ·
    refine ⟨1437574033962698387209735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1916765378616931182946313 1437574033962698387209735)
    ·
      refine ⟨2156361050944047580814603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1437574033962698387209735 2156361050944047580814603)
      ·
        refine ⟨3234541576416071371221905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2156361050944047580814603 3234541576416071371221905)
        ·
          refine ⟨2425906182312053528416429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3234541576416071371221905 2425906182312053528416429)
          ·
            refine ⟨909714818367020073156161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2425906182312053528416429 909714818367020073156161)
            ·
              refine ⟨682286113775265054867121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 909714818367020073156161 682286113775265054867121)
              ·
                refine ⟨511714585331448791150341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 682286113775265054867121 511714585331448791150341)
                ·
                  refine ⟨95946484749646648340689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 511714585331448791150341 95946484749646648340689)
                  ·
                    refine ⟨71959863562234986255517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 95946484749646648340689 71959863562234986255517)
                    ·
                      refine ⟨26984948835838119845819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 71959863562234986255517 26984948835838119845819)
                      ·
                        rfl

theorem cell23_52553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 4, 2, 3].length) (baseStart_52553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_52553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_52553 prefixEnd_52553 := by exact prefixLift 52553
  have htrace : WordTrace (prefixWord ++ tailWord_52553) baseStart_52553 baseEnd_52553 := by
    simpa [prefixWord, tailWord_52553, baseEnd_52553] using wordTrace_append hprefix tailTrace_52553
  have hstable : (prefixWord ++ tailWord_52553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52553).length < 2 ^ (prefixWord ++ tailWord_52553).sum := by decide
  have hdescent : baseEnd_52553 < baseStart_52553 := by decide
  rcases family_descends (prefixWord ++ tailWord_52553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
