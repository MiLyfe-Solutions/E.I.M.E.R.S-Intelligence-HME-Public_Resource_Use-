import V185TrunkScan23Chunk0148

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_880633 : List Nat := [1, 2, 1, 3, 1, 5, 1, 4, 1, 2, 2]
def baseStart_880633 : Nat := 118140960795 + 880633 * 2 ^ 59
def prefixEnd_880633 : Nat := 4983230072969 + 3 ^ 40 * 880633 * 2
def baseEnd_880633 : Nat := 452188009210958253037549

theorem tailTrace_880633 : CollatzResearch.WordTrace tailWord_880633 prefixEnd_880633 452188009210958253037549 := by
  unfold tailWord_880633
  simp only [CollatzResearch.WordTrace]
  refine ⟨32119324218624515987542553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21412882812416343991695035 32119324218624515987542553)
  ·
    refine ⟨24089493163968386990656915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32119324218624515987542553 24089493163968386990656915)
    ·
      refine ⟨36134239745952580485985373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24089493163968386990656915 36134239745952580485985373)
      ·
        refine ⟨13550339904732217682244515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36134239745952580485985373 13550339904732217682244515)
        ·
          refine ⟨20325509857098326523366773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13550339904732217682244515 20325509857098326523366773)
          ·
            refine ⟨1905516549102968111565635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20325509857098326523366773 1905516549102968111565635)
            ·
              refine ⟨2858274823654452167348453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1905516549102968111565635 2858274823654452167348453)
              ·
                refine ⟨535926529435209781377835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2858274823654452167348453 535926529435209781377835)
                ·
                  refine ⟨803889794152814672066753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 535926529435209781377835 803889794152814672066753)
                  ·
                    refine ⟨602917345614611004050065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 803889794152814672066753 602917345614611004050065)
                    ·
                      refine ⟨452188009210958253037549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 602917345614611004050065 452188009210958253037549)
                      ·
                        rfl

theorem cell23_880633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 4, 1, 2, 2].length) (baseStart_880633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_880633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_880633 prefixEnd_880633 := by exact prefixLift 880633
  have htrace : WordTrace (prefixWord ++ tailWord_880633) baseStart_880633 baseEnd_880633 := by
    simpa [prefixWord, tailWord_880633, baseEnd_880633] using wordTrace_append hprefix tailTrace_880633
  have hstable : (prefixWord ++ tailWord_880633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880633).length < 2 ^ (prefixWord ++ tailWord_880633).sum := by decide
  have hdescent : baseEnd_880633 < baseStart_880633 := by decide
  rcases family_descends (prefixWord ++ tailWord_880633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880635 : List Nat := [1, 1, 1, 1, 1, 3, 5, 1, 2, 7]
def baseStart_880635 : Nat := 118140960795 + 880635 * 2 ^ 59
def prefixEnd_880635 : Nat := 4983230072969 + 3 ^ 40 * 880635 * 2
def baseEnd_880635 : Nat := 150729678724089081737513

theorem tailTrace_880635 : CollatzResearch.WordTrace tailWord_880635 prefixEnd_880635 150729678724089081737513 := by
  unfold tailWord_880635
  simp only [CollatzResearch.WordTrace]
  refine ⟨32119397164617270329115359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21412931443078180219410239 32119397164617270329115359)
  ·
    refine ⟨48179095746925905493673039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32119397164617270329115359 48179095746925905493673039)
    ·
      refine ⟨72268643620388858240509559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48179095746925905493673039 72268643620388858240509559)
      ·
        refine ⟨108402965430583287360764339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72268643620388858240509559 108402965430583287360764339)
        ·
          refine ⟨162604448145874931041146509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108402965430583287360764339 162604448145874931041146509)
          ·
            refine ⟨60976668054703099140429941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162604448145874931041146509 60976668054703099140429941)
            ·
              refine ⟨5716562630128415544415307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60976668054703099140429941 5716562630128415544415307)
              ·
                refine ⟨8574843945192623316622961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5716562630128415544415307 8574843945192623316622961)
                ·
                  refine ⟨6431132958894467487467221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8574843945192623316622961 6431132958894467487467221)
                  ·
                    refine ⟨150729678724089081737513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6431132958894467487467221 150729678724089081737513)
                    ·
                      rfl

theorem cell23_880635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 7].length) (baseStart_880635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_880635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_880635 prefixEnd_880635 := by exact prefixLift 880635
  have htrace : WordTrace (prefixWord ++ tailWord_880635) baseStart_880635 baseEnd_880635 := by
    simpa [prefixWord, tailWord_880635, baseEnd_880635] using wordTrace_append hprefix tailTrace_880635
  have hstable : (prefixWord ++ tailWord_880635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880635).length < 2 ^ (prefixWord ++ tailWord_880635).sum := by decide
  have hdescent : baseEnd_880635 < baseStart_880635 := by decide
  rcases family_descends (prefixWord ++ tailWord_880635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880659 : List Nat := [1, 1, 1, 2, 1, 4, 4, 1, 3, 3, 2]
def baseStart_880659 : Nat := 118140960795 + 880659 * 2 ^ 59
def prefixEnd_880659 : Nat := 4983230072969 + 3 ^ 40 * 880659 * 2
def baseEnd_880659 : Nat := 452201359707975151312429

theorem tailTrace_880659 : CollatzResearch.WordTrace tailWord_880659 prefixEnd_880659 452201359707975151312429 := by
  unfold tailWord_880659
  simp only [CollatzResearch.WordTrace]
  refine ⟨32120272516530322427989031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21413515011020214951992687 32120272516530322427989031)
  ·
    refine ⟨48180408774795483641983547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32120272516530322427989031 48180408774795483641983547)
    ·
      refine ⟨72270613162193225462975321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48180408774795483641983547 72270613162193225462975321)
      ·
        refine ⟨54202959871644919097231491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72270613162193225462975321 54202959871644919097231491)
        ·
          refine ⟨81304439807467378645847237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54202959871644919097231491 81304439807467378645847237)
          ·
            refine ⟨15244582463900133496096357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81304439807467378645847237 15244582463900133496096357)
            ·
              refine ⟨2858359211981275030518067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15244582463900133496096357 2858359211981275030518067)
              ·
                refine ⟨4287538817971912545777101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2858359211981275030518067 4287538817971912545777101)
                ·
                  refine ⟨1607827056739467204666413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4287538817971912545777101 1607827056739467204666413)
                  ·
                    refine ⟨602935146277300201749905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1607827056739467204666413 602935146277300201749905)
                    ·
                      refine ⟨452201359707975151312429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 602935146277300201749905 452201359707975151312429)
                      ·
                        rfl

theorem cell23_880659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 3, 3, 2].length) (baseStart_880659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_880659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_880659 prefixEnd_880659 := by exact prefixLift 880659
  have htrace : WordTrace (prefixWord ++ tailWord_880659) baseStart_880659 baseEnd_880659 := by
    simpa [prefixWord, tailWord_880659, baseEnd_880659] using wordTrace_append hprefix tailTrace_880659
  have hstable : (prefixWord ++ tailWord_880659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880659).length < 2 ^ (prefixWord ++ tailWord_880659).sum := by decide
  have hdescent : baseEnd_880659 < baseStart_880659 := by decide
  rcases family_descends (prefixWord ++ tailWord_880659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880665 : List Nat := [1, 2, 1, 2, 1, 1, 3, 1, 3, 8]
def baseStart_880665 : Nat := 118140960795 + 880665 * 2 ^ 59
def prefixEnd_880665 : Nat := 4983230072969 + 3 ^ 40 * 880665 * 2
def baseEnd_880665 : Nat := 150734813530634042612467

theorem tailTrace_880665 : CollatzResearch.WordTrace tailWord_880665 prefixEnd_880665 150734813530634042612467 := by
  unfold tailWord_880665
  simp only [CollatzResearch.WordTrace]
  refine ⟨32120491354508585452707449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21413660903005723635138299 32120491354508585452707449)
  ·
    refine ⟨24090368515881439089530587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32120491354508585452707449 24090368515881439089530587)
    ·
      refine ⟨36135552773822158634295881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24090368515881439089530587 36135552773822158634295881)
      ·
        refine ⟨27101664580366618975721911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36135552773822158634295881 27101664580366618975721911)
        ·
          refine ⟨40652496870549928463582867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27101664580366618975721911 40652496870549928463582867)
          ·
            refine ⟨60978745305824892695374301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40652496870549928463582867 60978745305824892695374301)
            ·
              refine ⟨22867029489684334760765363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60978745305824892695374301 22867029489684334760765363)
              ·
                refine ⟨34300544234526502141148045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22867029489684334760765363 34300544234526502141148045)
                ·
                  refine ⟨12862704087947438302930517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34300544234526502141148045 12862704087947438302930517)
                  ·
                    refine ⟨150734813530634042612467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 12862704087947438302930517 150734813530634042612467)
                    ·
                      rfl

theorem cell23_880665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 8].length) (baseStart_880665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_880665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_880665 prefixEnd_880665 := by exact prefixLift 880665
  have htrace : WordTrace (prefixWord ++ tailWord_880665) baseStart_880665 baseEnd_880665 := by
    simpa [prefixWord, tailWord_880665, baseEnd_880665] using wordTrace_append hprefix tailTrace_880665
  have hstable : (prefixWord ++ tailWord_880665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880665).length < 2 ^ (prefixWord ++ tailWord_880665).sum := by decide
  have hdescent : baseEnd_880665 < baseStart_880665 := by decide
  rcases family_descends (prefixWord ++ tailWord_880665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880710 : List Nat := [6, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2]
def baseStart_880710 : Nat := 118140960795 + 880710 * 2 ^ 59
def prefixEnd_880710 : Nat := 4983230072969 + 3 ^ 40 * 880710 * 2
def baseEnd_880710 : Nat := 452227547221354451774695

theorem tailTrace_880710 : CollatzResearch.WordTrace tailWord_880710 prefixEnd_880710 452227547221354451774695 := by
  unfold tailWord_880710
  simp only [CollatzResearch.WordTrace]
  refine ⟨1003816644979548691815487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21414755092897038758730389 1003816644979548691815487)
  ·
    refine ⟨1505724967469323037723231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1003816644979548691815487 1505724967469323037723231)
    ·
      refine ⟨2258587451203984556584847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1505724967469323037723231 2258587451203984556584847)
      ·
        refine ⟨3387881176805976834877271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2258587451203984556584847 3387881176805976834877271)
        ·
          refine ⟨5081821765208965252315907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3387881176805976834877271 5081821765208965252315907)
          ·
            refine ⟨7622732647813447878473861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5081821765208965252315907 7622732647813447878473861)
            ·
              refine ⟨1429262371465021477213849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7622732647813447878473861 1429262371465021477213849)
              ·
                refine ⟨1071946778598766107910387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1429262371465021477213849 1071946778598766107910387)
                ·
                  refine ⟨1607920167898149161865581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1071946778598766107910387 1607920167898149161865581)
                  ·
                    refine ⟨602970062961805935699593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1607920167898149161865581 602970062961805935699593)
                    ·
                      refine ⟨452227547221354451774695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 602970062961805935699593 452227547221354451774695)
                      ·
                        rfl

theorem cell23_880710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_880710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_880710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_880710 prefixEnd_880710 := by exact prefixLift 880710
  have htrace : WordTrace (prefixWord ++ tailWord_880710) baseStart_880710 baseEnd_880710 := by
    simpa [prefixWord, tailWord_880710, baseEnd_880710] using wordTrace_append hprefix tailTrace_880710
  have hstable : (prefixWord ++ tailWord_880710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880710).length < 2 ^ (prefixWord ++ tailWord_880710).sum := by decide
  have hdescent : baseEnd_880710 < baseStart_880710 := by decide
  rcases family_descends (prefixWord ++ tailWord_880710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880726 : List Nat := [5, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5]
def baseStart_880726 : Nat := 118140960795 + 880726 * 2 ^ 59
def prefixEnd_880726 : Nat := 4983230072969 + 3 ^ 40 * 880726 * 2
def baseEnd_880726 : Nat := 452235762911826389174621

theorem tailTrace_880726 : CollatzResearch.WordTrace tailWord_880726 prefixEnd_880726 452235762911826389174621 := by
  unfold tailWord_880726
  simp only [CollatzResearch.WordTrace]
  refine ⟨2007669762955474554417377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21415144138191728580452021 2007669762955474554417377)
  ·
    refine ⟨1505752322216605915813033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2007669762955474554417377 1505752322216605915813033)
    ·
      refine ⟨1129314241662454436859775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1505752322216605915813033 1129314241662454436859775)
      ·
        refine ⟨1693971362493681655289663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1129314241662454436859775 1693971362493681655289663)
        ·
          refine ⟨2540957043740522482934495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1693971362493681655289663 2540957043740522482934495)
          ·
            refine ⟨3811435565610783724401743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2540957043740522482934495 3811435565610783724401743)
            ·
              refine ⟨5717153348416175586602615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3811435565610783724401743 5717153348416175586602615)
              ·
                refine ⟨8575730022624263379903923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5717153348416175586602615 8575730022624263379903923)
                ·
                  refine ⟨12863595033936395069855885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8575730022624263379903923 12863595033936395069855885)
                  ·
                    refine ⟨4823848137726148151195957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12863595033936395069855885 4823848137726148151195957)
                    ·
                      refine ⟨452235762911826389174621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4823848137726148151195957 452235762911826389174621)
                      ·
                        rfl

theorem cell23_880726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_880726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_880726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_880726 prefixEnd_880726 := by exact prefixLift 880726
  have htrace : WordTrace (prefixWord ++ tailWord_880726) baseStart_880726 baseEnd_880726 := by
    simpa [prefixWord, tailWord_880726, baseEnd_880726] using wordTrace_append hprefix tailTrace_880726
  have hstable : (prefixWord ++ tailWord_880726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880726).length < 2 ^ (prefixWord ++ tailWord_880726).sum := by decide
  have hdescent : baseEnd_880726 < baseStart_880726 := by decide
  rcases family_descends (prefixWord ++ tailWord_880726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880746 : List Nat := [3, 1, 3, 2, 3, 2, 1, 1, 7]
def baseStart_880746 : Nat := 118140960795 + 880746 * 2 ^ 59
def prefixEnd_880746 : Nat := 4983230072969 + 3 ^ 40 * 880746 * 2
def baseEnd_880746 : Nat := 50249559169435145658281

theorem tailTrace_880746 : CollatzResearch.WordTrace tailWord_880746 prefixEnd_880746 50249559169435145658281 := by
  unfold tailWord_880746
  simp only [CollatzResearch.WordTrace]
  refine ⟨8030861416803784071601523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21415630444810090857604061 8030861416803784071601523)
  ·
    refine ⟨12046292125205676107402285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8030861416803784071601523 12046292125205676107402285)
    ·
      refine ⟨4517359546952128540275857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12046292125205676107402285 4517359546952128540275857)
      ·
        refine ⟨3388019660214096405206893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4517359546952128540275857 3388019660214096405206893)
        ·
          refine ⟨1270507372580286151952585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3388019660214096405206893 1270507372580286151952585)
          ·
            refine ⟨952880529435214613964439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1270507372580286151952585 952880529435214613964439)
            ·
              refine ⟨1429320794152821920946659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 952880529435214613964439 1429320794152821920946659)
              ·
                refine ⟨2143981191229232881419989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1429320794152821920946659 2143981191229232881419989)
                ·
                  refine ⟨50249559169435145658281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2143981191229232881419989 50249559169435145658281)
                  ·
                    rfl

theorem cell23_880746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 7].length) (baseStart_880746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_880746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_880746 prefixEnd_880746 := by exact prefixLift 880746
  have htrace : WordTrace (prefixWord ++ tailWord_880746) baseStart_880746 baseEnd_880746 := by
    simpa [prefixWord, tailWord_880746, baseEnd_880746] using wordTrace_append hprefix tailTrace_880746
  have hstable : (prefixWord ++ tailWord_880746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880746).length < 2 ^ (prefixWord ++ tailWord_880746).sum := by decide
  have hdescent : baseEnd_880746 < baseStart_880746 := by decide
  rcases family_descends (prefixWord ++ tailWord_880746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880752 : List Nat := [2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 7]
def baseStart_880752 : Nat := 118140960795 + 880752 * 2 ^ 59
def prefixEnd_880752 : Nat := 4983230072969 + 3 ^ 40 * 880752 * 2
def baseEnd_880752 : Nat := 452249113408843287449501

theorem tailTrace_880752 : CollatzResearch.WordTrace tailWord_880752 prefixEnd_880752 452249113408843287449501 := by
  unfold tailWord_880752
  simp only [CollatzResearch.WordTrace]
  refine ⟨16061832252596699655562255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21415776336795599540749673 16061832252596699655562255)
  ·
    refine ⟨24092748378895049483343383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16061832252596699655562255 24092748378895049483343383)
    ·
      refine ⟨36139122568342574225015075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24092748378895049483343383 36139122568342574225015075)
      ·
        refine ⟨54208683852513861337522613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36139122568342574225015075 54208683852513861337522613)
        ·
          refine ⟨5082064111173174500392745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54208683852513861337522613 5082064111173174500392745)
          ·
            refine ⟨3811548083379880875294559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5082064111173174500392745 3811548083379880875294559)
            ·
              refine ⟨5717322125069821312941839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3811548083379880875294559 5717322125069821312941839)
              ·
                refine ⟨8575983187604731969412759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5717322125069821312941839 8575983187604731969412759)
                ·
                  refine ⟨12863974781407097954119139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8575983187604731969412759 12863974781407097954119139)
                  ·
                    refine ⟨19295962172110646931178709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12863974781407097954119139 19295962172110646931178709)
                    ·
                      refine ⟨452249113408843287449501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 19295962172110646931178709 452249113408843287449501)
                      ·
                        rfl

theorem cell23_880752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 7].length) (baseStart_880752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_880752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_880752 prefixEnd_880752 := by exact prefixLift 880752
  have htrace : WordTrace (prefixWord ++ tailWord_880752) baseStart_880752 baseEnd_880752 := by
    simpa [prefixWord, tailWord_880752, baseEnd_880752] using wordTrace_append hprefix tailTrace_880752
  have hstable : (prefixWord ++ tailWord_880752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880752).length < 2 ^ (prefixWord ++ tailWord_880752).sum := by decide
  have hdescent : baseEnd_880752 < baseStart_880752 := by decide
  rcases family_descends (prefixWord ++ tailWord_880752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880776 : List Nat := [2, 1, 3, 4, 1, 2, 2, 1, 2, 5]
def baseStart_880776 : Nat := 118140960795 + 880776 * 2 ^ 59
def prefixEnd_880776 : Nat := 4983230072969 + 3 ^ 40 * 880776 * 2
def baseEnd_880776 : Nat := 150753812314850397849797

theorem tailTrace_880776 : CollatzResearch.WordTrace tailWord_880776 prefixEnd_880776 150753812314850397849797 := by
  unfold tailWord_880776
  simp only [CollatzResearch.WordTrace]
  refine ⟨16062269928553225704999091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21416359904737634273332121 16062269928553225704999091)
  ·
    refine ⟨24093404892829838557498637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16062269928553225704999091 24093404892829838557498637)
    ·
      refine ⟨9035026834811189459061989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24093404892829838557498637 9035026834811189459061989)
      ·
        refine ⟨1694067531527098023574123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9035026834811189459061989 1694067531527098023574123)
        ·
          refine ⟨2541101297290647035361185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1694067531527098023574123 2541101297290647035361185)
          ·
            refine ⟨1905825972967985276520889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2541101297290647035361185 1905825972967985276520889)
            ·
              refine ⟨1429369479725988957390667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1905825972967985276520889 1429369479725988957390667)
              ·
                refine ⟨2144054219588983436086001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1429369479725988957390667 2144054219588983436086001)
                ·
                  refine ⟨1608040664691737577064501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2144054219588983436086001 1608040664691737577064501)
                  ·
                    refine ⟨150753812314850397849797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1608040664691737577064501 150753812314850397849797)
                    ·
                      rfl

theorem cell23_880776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 1, 2, 5].length) (baseStart_880776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_880776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_880776 prefixEnd_880776 := by exact prefixLift 880776
  have htrace : WordTrace (prefixWord ++ tailWord_880776) baseStart_880776 baseEnd_880776 := by
    simpa [prefixWord, tailWord_880776, baseEnd_880776] using wordTrace_append hprefix tailTrace_880776
  have hstable : (prefixWord ++ tailWord_880776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880776).length < 2 ^ (prefixWord ++ tailWord_880776).sum := by decide
  have hdescent : baseEnd_880776 < baseStart_880776 := by decide
  rcases family_descends (prefixWord ++ tailWord_880776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880779 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 6, 4, 2]
def baseStart_880779 : Nat := 118140960795 + 880779 * 2 ^ 59
def prefixEnd_880779 : Nat := 4983230072969 + 3 ^ 40 * 880779 * 2
def baseEnd_880779 : Nat := 452262977386514681811877

theorem tailTrace_880779 : CollatzResearch.WordTrace tailWord_880779 prefixEnd_880779 452262977386514681811877 := by
  unfold tailWord_880779
  simp only [CollatzResearch.WordTrace]
  refine ⟨32124649276095582922357391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21416432850730388614904927 32124649276095582922357391)
  ·
    refine ⟨48186973914143374383536087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32124649276095582922357391 48186973914143374383536087)
    ·
      refine ⟨72280460871215061575304131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48186973914143374383536087 72280460871215061575304131)
      ·
        refine ⟨108420691306822592362956197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72280460871215061575304131 108420691306822592362956197)
        ·
          refine ⟨20328879620029236068054287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108420691306822592362956197 20328879620029236068054287)
          ·
            refine ⟨30493319430043854102081431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20328879620029236068054287 30493319430043854102081431)
            ·
              refine ⟨45739979145065781153122147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30493319430043854102081431 45739979145065781153122147)
              ·
                refine ⟨68609968717598671729683221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45739979145065781153122147 68609968717598671729683221)
                ·
                  refine ⟨3216092283637437737328901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 68609968717598671729683221 3216092283637437737328901)
                  ·
                    refine ⟨603017303182019575749169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3216092283637437737328901 603017303182019575749169)
                    ·
                      refine ⟨452262977386514681811877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 603017303182019575749169 452262977386514681811877)
                      ·
                        rfl

theorem cell23_880779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 6, 4, 2].length) (baseStart_880779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_880779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_880779 prefixEnd_880779 := by exact prefixLift 880779
  have htrace : WordTrace (prefixWord ++ tailWord_880779) baseStart_880779 baseEnd_880779 := by
    simpa [prefixWord, tailWord_880779, baseEnd_880779] using wordTrace_append hprefix tailTrace_880779
  have hstable : (prefixWord ++ tailWord_880779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880779).length < 2 ^ (prefixWord ++ tailWord_880779).sum := by decide
  have hdescent : baseEnd_880779 < baseStart_880779 := by decide
  rcases family_descends (prefixWord ++ tailWord_880779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880796 : List Nat := [2, 2, 3, 2, 1, 1, 2, 2, 2, 4, 2]
def baseStart_880796 : Nat := 118140960795 + 880796 * 2 ^ 59
def prefixEnd_880796 : Nat := 4983230072969 + 3 ^ 40 * 880796 * 2
def baseEnd_880796 : Nat := 452271706557641115299299

theorem tailTrace_880796 : CollatzResearch.WordTrace tailWord_880796 prefixEnd_880796 452271706557641115299299 := by
  unfold tailWord_880796
  simp only [CollatzResearch.WordTrace]
  refine ⟨16062634658516997412863121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21416846211355996550484161 16062634658516997412863121)
  ·
    refine ⟨12046975993887748059647341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16062634658516997412863121 12046975993887748059647341)
    ·
      refine ⟨4517615997707905522367753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12046975993887748059647341 4517615997707905522367753)
      ·
        refine ⟨3388211998280929141775815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4517615997707905522367753 3388211998280929141775815)
        ·
          refine ⟨5082317997421393712663723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3388211998280929141775815 5082317997421393712663723)
          ·
            refine ⟨7623476996132090568995585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5082317997421393712663723 7623476996132090568995585)
            ·
              refine ⟨5717607747099067926746689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7623476996132090568995585 5717607747099067926746689)
              ·
                refine ⟨4288205810324300945060017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5717607747099067926746689 4288205810324300945060017)
                ·
                  refine ⟨3216154357743225708795013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4288205810324300945060017 3216154357743225708795013)
                  ·
                    refine ⟨603028942076854820399065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3216154357743225708795013 603028942076854820399065)
                    ·
                      refine ⟨452271706557641115299299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 603028942076854820399065 452271706557641115299299)
                      ·
                        rfl

theorem cell23_880796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_880796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_880796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_880796 prefixEnd_880796 := by exact prefixLift 880796
  have htrace : WordTrace (prefixWord ++ tailWord_880796) baseStart_880796 baseEnd_880796 := by
    simpa [prefixWord, tailWord_880796, baseEnd_880796] using wordTrace_append hprefix tailTrace_880796
  have hstable : (prefixWord ++ tailWord_880796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880796).length < 2 ^ (prefixWord ++ tailWord_880796).sum := by decide
  have hdescent : baseEnd_880796 < baseStart_880796 := by decide
  rcases family_descends (prefixWord ++ tailWord_880796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880813 : List Nat := [1, 5, 2, 1, 2, 2, 1, 1, 2, 4, 2]
def baseStart_880813 : Nat := 118140960795 + 880813 * 2 ^ 59
def prefixEnd_880813 : Nat := 4983230072969 + 3 ^ 40 * 880813 * 2
def baseEnd_880813 : Nat := 452280435728767548786721

theorem tailTrace_880813 : CollatzResearch.WordTrace tailWord_880813 prefixEnd_880813 452280435728767548786721 := by
  unfold tailWord_880813
  simp only [CollatzResearch.WordTrace]
  refine ⟨32125889357972406729095093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21417259571981604486063395 32125889357972406729095093)
  ·
    refine ⟨3011802127309913130852665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32125889357972406729095093 3011802127309913130852665)
    ·
      refine ⟨2258851595482434848139499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3011802127309913130852665 2258851595482434848139499)
      ·
        refine ⟨3388277393223652272209249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2258851595482434848139499 3388277393223652272209249)
        ·
          refine ⟨2541208044917739204156937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3388277393223652272209249 2541208044917739204156937)
          ·
            refine ⟨1905906033688304403117703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2541208044917739204156937 1905906033688304403117703)
            ·
              refine ⟨2858859050532456604676555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1905906033688304403117703 2858859050532456604676555)
              ·
                refine ⟨4288288575798684907014833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2858859050532456604676555 4288288575798684907014833)
                ·
                  refine ⟨3216216431849013680261125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4288288575798684907014833 3216216431849013680261125)
                  ·
                    refine ⟨603040580971690065048961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3216216431849013680261125 603040580971690065048961)
                    ·
                      refine ⟨452280435728767548786721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 603040580971690065048961 452280435728767548786721)
                      ·
                        rfl

theorem cell23_880813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_880813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_880813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_880813 prefixEnd_880813 := by exact prefixLift 880813
  have htrace : WordTrace (prefixWord ++ tailWord_880813) baseStart_880813 baseEnd_880813 := by
    simpa [prefixWord, tailWord_880813, baseEnd_880813] using wordTrace_append hprefix tailTrace_880813
  have hstable : (prefixWord ++ tailWord_880813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880813).length < 2 ^ (prefixWord ++ tailWord_880813).sum := by decide
  have hdescent : baseEnd_880813 < baseStart_880813 := by decide
  rcases family_descends (prefixWord ++ tailWord_880813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880830 : List Nat := [4, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4]
def baseStart_880830 : Nat := 118140960795 + 880830 * 2 ^ 59
def prefixEnd_880830 : Nat := 4983230072969 + 3 ^ 40 * 880830 * 2
def baseEnd_880830 : Nat := 452289164899893982274143

theorem tailTrace_880830 : CollatzResearch.WordTrace tailWord_880830 prefixEnd_880830 452289164899893982274143 := by
  unfold tailWord_880830
  simp only [CollatzResearch.WordTrace]
  refine ⟨4015813674863852329057993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21417672932607212421642629 4015813674863852329057993)
  ·
    refine ⟨3011860256147889246793495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4015813674863852329057993 3011860256147889246793495)
    ·
      refine ⟨4517790384221833870190243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3011860256147889246793495 4517790384221833870190243)
      ·
        refine ⟨6776685576332750805285365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4517790384221833870190243 6776685576332750805285365)
        ·
          refine ⟨635314272781195387995503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6776685576332750805285365 635314272781195387995503)
          ·
            refine ⟨952971409171793081993255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 635314272781195387995503 952971409171793081993255)
            ·
              refine ⟨1429457113757689622989883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 952971409171793081993255 1429457113757689622989883)
              ·
                refine ⟨2144185670636534434484825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1429457113757689622989883 2144185670636534434484825)
                ·
                  refine ⟨1608139252977400825863619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2144185670636534434484825 1608139252977400825863619)
                  ·
                    refine ⟨2412208879466101238795429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1608139252977400825863619 2412208879466101238795429)
                    ·
                      refine ⟨452289164899893982274143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2412208879466101238795429 452289164899893982274143)
                      ·
                        rfl

theorem cell23_880830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4].length) (baseStart_880830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_880830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_880830 prefixEnd_880830 := by exact prefixLift 880830
  have htrace : WordTrace (prefixWord ++ tailWord_880830) baseStart_880830 baseEnd_880830 := by
    simpa [prefixWord, tailWord_880830, baseEnd_880830] using wordTrace_append hprefix tailTrace_880830
  have hstable : (prefixWord ++ tailWord_880830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880830).length < 2 ^ (prefixWord ++ tailWord_880830).sum := by decide
  have hdescent : baseEnd_880830 < baseStart_880830 := by decide
  rcases family_descends (prefixWord ++ tailWord_880830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880833 : List Nat := [1, 2, 6, 1, 2, 1, 1, 1, 1, 4, 3]
def baseStart_880833 : Nat := 118140960795 + 880833 * 2 ^ 59
def prefixEnd_880833 : Nat := 4983230072969 + 3 ^ 40 * 880833 * 2
def baseEnd_880833 : Nat := 452290705341857470536629

theorem tailTrace_880833 : CollatzResearch.WordTrace tailWord_880833 prefixEnd_880833 452290705341857470536629 := by
  unfold tailWord_880833
  simp only [CollatzResearch.WordTrace]
  refine ⟨32126618817899950144823153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21417745878599966763215435 32126618817899950144823153)
  ·
    refine ⟨24094964113424962608617365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32126618817899950144823153 24094964113424962608617365)
    ·
      refine ⟨1129451442816795122278939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 24094964113424962608617365 1129451442816795122278939)
      ·
        refine ⟨1694177164225192683418409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1129451442816795122278939 1694177164225192683418409)
        ·
          refine ⟨1270632873168894512563807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1694177164225192683418409 1270632873168894512563807)
          ·
            refine ⟨1905949309753341768845711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1270632873168894512563807 1905949309753341768845711)
            ·
              refine ⟨2858923964630012653268567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1905949309753341768845711 2858923964630012653268567)
              ·
                refine ⟨4288385946945018979902851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2858923964630012653268567 4288385946945018979902851)
                ·
                  refine ⟨6432578920417528469854277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4288385946945018979902851 6432578920417528469854277)
                  ·
                    refine ⟨1206108547578286588097677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6432578920417528469854277 1206108547578286588097677)
                    ·
                      refine ⟨452290705341857470536629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1206108547578286588097677 452290705341857470536629)
                      ·
                        rfl

theorem cell23_880833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_880833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_880833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_880833 prefixEnd_880833 := by exact prefixLift 880833
  have htrace : WordTrace (prefixWord ++ tailWord_880833) baseStart_880833 baseEnd_880833 := by
    simpa [prefixWord, tailWord_880833, baseEnd_880833] using wordTrace_append hprefix tailTrace_880833
  have hstable : (prefixWord ++ tailWord_880833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880833).length < 2 ^ (prefixWord ++ tailWord_880833).sum := by decide
  have hdescent : baseEnd_880833 < baseStart_880833 := by decide
  rcases family_descends (prefixWord ++ tailWord_880833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880853 : List Nat := [1, 3, 2, 4, 2, 2, 1, 2, 6]
def baseStart_880853 : Nat := 118140960795 + 880853 * 2 ^ 59
def prefixEnd_880853 : Nat := 4983230072969 + 3 ^ 40 * 880853 * 2
def baseEnd_880853 : Nat := 50255663883883043587393

theorem tailTrace_880853 : CollatzResearch.WordTrace tailWord_880853 prefixEnd_880853 50255663883883043587393 := by
  unfold tailWord_880853
  simp only [CollatzResearch.WordTrace]
  refine ⟨32127348277827493560551213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21418232185218329040367475 32127348277827493560551213)
  ·
    refine ⟨12047755604185310085206705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32127348277827493560551213 12047755604185310085206705)
    ·
      refine ⟨9035816703138982563905029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12047755604185310085206705 9035816703138982563905029)
      ·
        refine ⟨1694215631838559230732193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9035816703138982563905029 1694215631838559230732193)
        ·
          refine ⟨1270661723878919423049145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1694215631838559230732193 1270661723878919423049145)
          ·
            refine ⟨952996292909189567286859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1270661723878919423049145 952996292909189567286859)
            ·
              refine ⟨1429494439363784350930289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 952996292909189567286859 1429494439363784350930289)
              ·
                refine ⟨1072120829522838263197717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1429494439363784350930289 1072120829522838263197717)
                ·
                  refine ⟨50255663883883043587393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1072120829522838263197717 50255663883883043587393)
                  ·
                    rfl

theorem cell23_880853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 2, 6].length) (baseStart_880853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_880853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_880853 prefixEnd_880853 := by exact prefixLift 880853
  have htrace : WordTrace (prefixWord ++ tailWord_880853) baseStart_880853 baseEnd_880853 := by
    simpa [prefixWord, tailWord_880853, baseEnd_880853] using wordTrace_append hprefix tailTrace_880853
  have hstable : (prefixWord ++ tailWord_880853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880853).length < 2 ^ (prefixWord ++ tailWord_880853).sum := by decide
  have hdescent : baseEnd_880853 < baseStart_880853 := by decide
  rcases family_descends (prefixWord ++ tailWord_880853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880886 : List Nat := [5, 1, 1, 1, 1, 1, 2, 3, 3, 1, 4]
def baseStart_880886 : Nat := 118140960795 + 880886 * 2 ^ 59
def prefixEnd_880886 : Nat := 4983230072969 + 3 ^ 40 * 880886 * 2
def baseEnd_880886 : Nat := 452317919816545763173885

theorem tailTrace_880886 : CollatzResearch.WordTrace tailWord_880886 prefixEnd_880886 452317919816545763173885 := by
  unfold tailWord_880886
  simp only [CollatzResearch.WordTrace]
  refine ⟨2008034492919246262281407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21419034591138626797668341 2008034492919246262281407)
  ·
    refine ⟨3012051739378869393422111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2008034492919246262281407 3012051739378869393422111)
    ·
      refine ⟨4518077609068304090133167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3012051739378869393422111 4518077609068304090133167)
      ·
        refine ⟨6777116413602456135199751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4518077609068304090133167 6777116413602456135199751)
        ·
          refine ⟨10165674620403684202799627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6777116413602456135199751 10165674620403684202799627)
          ·
            refine ⟨15248511930605526304199441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10165674620403684202799627 15248511930605526304199441)
            ·
              refine ⟨11436383947954144728149581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15248511930605526304199441 11436383947954144728149581)
              ·
                refine ⟨4288643980482804273056093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11436383947954144728149581 4288643980482804273056093)
                ·
                  refine ⟨1608241492681051602396035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4288643980482804273056093 1608241492681051602396035)
                  ·
                    refine ⟨2412362239021577403594053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1608241492681051602396035 2412362239021577403594053)
                    ·
                      refine ⟨452317919816545763173885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2412362239021577403594053 452317919816545763173885)
                      ·
                        rfl

theorem cell23_880886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_880886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_880886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_880886 prefixEnd_880886 := by exact prefixLift 880886
  have htrace : WordTrace (prefixWord ++ tailWord_880886) baseStart_880886 baseEnd_880886 := by
    simpa [prefixWord, tailWord_880886, baseEnd_880886] using wordTrace_append hprefix tailTrace_880886
  have hstable : (prefixWord ++ tailWord_880886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880886).length < 2 ^ (prefixWord ++ tailWord_880886).sum := by decide
  have hdescent : baseEnd_880886 < baseStart_880886 := by decide
  rcases family_descends (prefixWord ++ tailWord_880886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880899 : List Nat := [1, 1, 1, 3, 2, 3, 2, 1, 3, 2, 4]
def baseStart_880899 : Nat := 118140960795 + 880899 * 2 ^ 59
def prefixEnd_880899 : Nat := 4983230072969 + 3 ^ 40 * 880899 * 2
def baseEnd_880899 : Nat := 452324595065054212311325

theorem tailTrace_880899 : CollatzResearch.WordTrace tailWord_880899 prefixEnd_880899 452324595065054212311325 := by
  unfold tailWord_880899
  simp only [CollatzResearch.WordTrace]
  refine ⟨32129026035660843416725751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21419350690440562277817167 32129026035660843416725751)
  ·
    refine ⟨48193539053491265125088627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32129026035660843416725751 48193539053491265125088627)
    ·
      refine ⟨72290308580236897687632941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48193539053491265125088627 72290308580236897687632941)
      ·
        refine ⟨27108865717588836632862353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72290308580236897687632941 27108865717588836632862353)
        ·
          refine ⟨20331649288191627474646765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27108865717588836632862353 20331649288191627474646765)
          ·
            refine ⟨7624368483071860302992537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20331649288191627474646765 7624368483071860302992537)
            ·
              refine ⟨5718276362303895227244403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7624368483071860302992537 5718276362303895227244403)
              ·
                refine ⟨8577414543455842840866605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5718276362303895227244403 8577414543455842840866605)
                ·
                  refine ⟨3216530453795941065324977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8577414543455842840866605 3216530453795941065324977)
                  ·
                    refine ⟨2412397840346955798993733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3216530453795941065324977 2412397840346955798993733)
                    ·
                      refine ⟨452324595065054212311325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2412397840346955798993733 452324595065054212311325)
                      ·
                        rfl

theorem cell23_880899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 3, 2, 4].length) (baseStart_880899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_880899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_880899 prefixEnd_880899 := by exact prefixLift 880899
  have htrace : WordTrace (prefixWord ++ tailWord_880899) baseStart_880899 baseEnd_880899 := by
    simpa [prefixWord, tailWord_880899, baseEnd_880899] using wordTrace_append hprefix tailTrace_880899
  have hstable : (prefixWord ++ tailWord_880899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880899).length < 2 ^ (prefixWord ++ tailWord_880899).sum := by decide
  have hdescent : baseEnd_880899 < baseStart_880899 := by decide
  rcases family_descends (prefixWord ++ tailWord_880899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880930 : List Nat := [3, 3, 1, 1, 3, 1, 4, 1, 2, 4]
def baseStart_880930 : Nat := 118140960795 + 880930 * 2 ^ 59
def prefixEnd_880930 : Nat := 4983230072969 + 3 ^ 40 * 880930 * 2
def baseEnd_880930 : Nat := 150780170988447863674561

theorem tailTrace_880930 : CollatzResearch.WordTrace tailWord_880930 prefixEnd_880930 150780170988447863674561 := by
  unfold tailWord_880930
  simp only [CollatzResearch.WordTrace]
  refine ⟨8032539174637133927776061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21420104465699023807402829 8032539174637133927776061)
  ·
    refine ⟨3012202190488925222916023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8032539174637133927776061 3012202190488925222916023)
    ·
      refine ⟨4518303285733387834374035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3012202190488925222916023 4518303285733387834374035)
      ·
        refine ⟨6777454928600081751561053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4518303285733387834374035 6777454928600081751561053)
        ·
          refine ⟨2541545598225030656835395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6777454928600081751561053 2541545598225030656835395)
          ·
            refine ⟨3812318397337545985253093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2541545598225030656835395 3812318397337545985253093)
            ·
              refine ⟨714809699500789872234955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3812318397337545985253093 714809699500789872234955)
              ·
                refine ⟨1072214549251184808352433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 714809699500789872234955 1072214549251184808352433)
                ·
                  refine ⟨804160911938388606264325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1072214549251184808352433 804160911938388606264325)
                  ·
                    refine ⟨150780170988447863674561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 804160911938388606264325 150780170988447863674561)
                    ·
                      rfl

theorem cell23_880930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 4, 1, 2, 4].length) (baseStart_880930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_880930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_880930 prefixEnd_880930 := by exact prefixLift 880930
  have htrace : WordTrace (prefixWord ++ tailWord_880930) baseStart_880930 baseEnd_880930 := by
    simpa [prefixWord, tailWord_880930, baseEnd_880930] using wordTrace_append hprefix tailTrace_880930
  have hstable : (prefixWord ++ tailWord_880930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880930).length < 2 ^ (prefixWord ++ tailWord_880930).sum := by decide
  have hdescent : baseEnd_880930 < baseStart_880930 := by decide
  rcases family_descends (prefixWord ++ tailWord_880930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880953 : List Nat := [1, 2, 1, 6, 1, 2, 1, 2, 1, 3, 3]
def baseStart_880953 : Nat := 118140960795 + 880953 * 2 ^ 59
def prefixEnd_880953 : Nat := 4983230072969 + 3 ^ 40 * 880953 * 2
def baseEnd_880953 : Nat := 452352323020397001036077

theorem tailTrace_880953 : CollatzResearch.WordTrace tailWord_880953 prefixEnd_880953 452352323020397001036077 := by
  unfold tailWord_880953
  simp only [CollatzResearch.WordTrace]
  refine ⟨32130995577465210639191513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21420663718310140426127675 32130995577465210639191513)
  ·
    refine ⟨24098246683098907979393635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32130995577465210639191513 24098246683098907979393635)
    ·
      refine ⟨36147370024648361969090453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24098246683098907979393635 36147370024648361969090453)
      ·
        refine ⟨1694407969905391967301115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 36147370024648361969090453 1694407969905391967301115)
        ·
          refine ⟨2541611954858087950951673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1694407969905391967301115 2541611954858087950951673)
          ·
            refine ⟨1906208966143565963213755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2541611954858087950951673 1906208966143565963213755)
            ·
              refine ⟨2859313449215348944820633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1906208966143565963213755 2859313449215348944820633)
              ·
                refine ⟨2144485086911511708615475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2859313449215348944820633 2144485086911511708615475)
                ·
                  refine ⟨3216727630367267562923213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2144485086911511708615475 3216727630367267562923213)
                  ·
                    refine ⟨1206272861387725336096205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3216727630367267562923213 1206272861387725336096205)
                    ·
                      refine ⟨452352323020397001036077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1206272861387725336096205 452352323020397001036077)
                      ·
                        rfl

theorem cell23_880953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_880953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_880953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_880953 prefixEnd_880953 := by exact prefixLift 880953
  have htrace : WordTrace (prefixWord ++ tailWord_880953) baseStart_880953 baseEnd_880953 := by
    simpa [prefixWord, tailWord_880953, baseEnd_880953] using wordTrace_append hprefix tailTrace_880953
  have hstable : (prefixWord ++ tailWord_880953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880953).length < 2 ^ (prefixWord ++ tailWord_880953).sum := by decide
  have hdescent : baseEnd_880953 < baseStart_880953 := by decide
  rcases family_descends (prefixWord ++ tailWord_880953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880963 : List Nat := [1, 1, 1, 3, 1, 3, 2, 5, 1, 3, 2]
def baseStart_880963 : Nat := 118140960795 + 880963 * 2 ^ 59
def prefixEnd_880963 : Nat := 4983230072969 + 3 ^ 40 * 880963 * 2
def baseEnd_880963 : Nat := 452357457826941961911031

theorem tailTrace_880963 : CollatzResearch.WordTrace tailWord_880963 prefixEnd_880963 452357457826941961911031 := by
  unfold tailWord_880963
  simp only [CollatzResearch.WordTrace]
  refine ⟨32131360307428982347055543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21420906871619321564703695 32131360307428982347055543)
  ·
    refine ⟨48197040461143473520583315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32131360307428982347055543 48197040461143473520583315)
    ·
      refine ⟨72295560691715210280874973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48197040461143473520583315 72295560691715210280874973)
      ·
        refine ⟨27110835259393203855328115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72295560691715210280874973 27110835259393203855328115)
        ·
          refine ⟨40666252889089805782992173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27110835259393203855328115 40666252889089805782992173)
          ·
            refine ⟨15249844833408677168622065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40666252889089805782992173 15249844833408677168622065)
            ·
              refine ⟨11437383625056507876466549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15249844833408677168622065 11437383625056507876466549)
              ·
                refine ⟨1072254714849047613418739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11437383625056507876466549 1072254714849047613418739)
                ·
                  refine ⟨1608382072273571420128109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1072254714849047613418739 1608382072273571420128109)
                  ·
                    refine ⟨603143277102589282548041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1608382072273571420128109 603143277102589282548041)
                    ·
                      refine ⟨452357457826941961911031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 603143277102589282548041 452357457826941961911031)
                      ·
                        rfl

theorem cell23_880963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 1, 3, 2].length) (baseStart_880963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_880963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_880963 prefixEnd_880963 := by exact prefixLift 880963
  have htrace : WordTrace (prefixWord ++ tailWord_880963) baseStart_880963 baseEnd_880963 := by
    simpa [prefixWord, tailWord_880963, baseEnd_880963] using wordTrace_append hprefix tailTrace_880963
  have hstable : (prefixWord ++ tailWord_880963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880963).length < 2 ^ (prefixWord ++ tailWord_880963).sum := by decide
  have hdescent : baseEnd_880963 < baseStart_880963 := by decide
  rcases family_descends (prefixWord ++ tailWord_880963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880969 : List Nat := [1, 2, 1, 1, 2, 3, 1, 4, 2, 6]
def baseStart_880969 : Nat := 118140960795 + 880969 * 2 ^ 59
def prefixEnd_880969 : Nat := 4983230072969 + 3 ^ 40 * 880969 * 2
def baseEnd_880969 : Nat := 150786846236956312812001

theorem tailTrace_880969 : CollatzResearch.WordTrace tailWord_880969 prefixEnd_880969 150786846236956312812001 := by
  unfold tailWord_880969
  simp only [CollatzResearch.WordTrace]
  refine ⟨32131579145407245371773961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21421052763604830247849307 32131579145407245371773961)
  ·
    refine ⟨24098684359055434028830471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32131579145407245371773961 24098684359055434028830471)
    ·
      refine ⟨36148026538583151043245707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24098684359055434028830471 36148026538583151043245707)
      ·
        refine ⟨54222039807874726564868561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36148026538583151043245707 54222039807874726564868561)
        ·
          refine ⟨40666529855906044923651421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54222039807874726564868561 40666529855906044923651421)
          ·
            refine ⟨15249948695964766846369283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40666529855906044923651421 15249948695964766846369283)
            ·
              refine ⟨22874923043947150269553925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15249948695964766846369283 22874923043947150269553925)
              ·
                refine ⟨4289048070740090675541361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22874923043947150269553925 4289048070740090675541361)
                ·
                  refine ⟨3216786053055068006656021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4289048070740090675541361 3216786053055068006656021)
                  ·
                    refine ⟨150786846236956312812001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3216786053055068006656021 150786846236956312812001)
                    ·
                      rfl

theorem cell23_880969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 2, 6].length) (baseStart_880969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_880969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_880969 prefixEnd_880969 := by exact prefixLift 880969
  have htrace : WordTrace (prefixWord ++ tailWord_880969) baseStart_880969 baseEnd_880969 := by
    simpa [prefixWord, tailWord_880969, baseEnd_880969] using wordTrace_append hprefix tailTrace_880969
  have hstable : (prefixWord ++ tailWord_880969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880969).length < 2 ^ (prefixWord ++ tailWord_880969).sum := by decide
  have hdescent : baseEnd_880969 < baseStart_880969 := by decide
  rcases family_descends (prefixWord ++ tailWord_880969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880979 : List Nat := [1, 1, 1, 2, 1, 1, 4, 2, 4, 1, 5]
def baseStart_880979 : Nat := 118140960795 + 880979 * 2 ^ 59
def prefixEnd_880979 : Nat := 4983230072969 + 3 ^ 40 * 880979 * 2
def baseEnd_880979 : Nat := 452365673517413899310957

theorem tailTrace_880979 : CollatzResearch.WordTrace tailWord_880979 prefixEnd_880979 452365673517413899310957 := by
  unfold tailWord_880979
  simp only [CollatzResearch.WordTrace]
  refine ⟨32131943875371017079637991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21421295916914011386425327 32131943875371017079637991)
  ·
    refine ⟨48197915813056525619456987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32131943875371017079637991 48197915813056525619456987)
    ·
      refine ⟨72296873719584788429185481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48197915813056525619456987 72296873719584788429185481)
      ·
        refine ⟨54222655289688591321889111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72296873719584788429185481 54222655289688591321889111)
        ·
          refine ⟨81333982934532886982833667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54222655289688591321889111 81333982934532886982833667)
          ·
            refine ⟨122000974401799330474250501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81333982934532886982833667 122000974401799330474250501)
            ·
              refine ⟨22875182700337374463921969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122000974401799330474250501 22875182700337374463921969)
              ·
                refine ⟨17156387025253030847941477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22875182700337374463921969 17156387025253030847941477)
                ·
                  refine ⟨3216822567234943283989027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17156387025253030847941477 3216822567234943283989027)
                  ·
                    refine ⟨4825233850852414925983541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3216822567234943283989027 4825233850852414925983541)
                    ·
                      refine ⟨452365673517413899310957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4825233850852414925983541 452365673517413899310957)
                      ·
                        rfl

theorem cell23_880979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 4, 1, 5].length) (baseStart_880979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_880979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_880979 prefixEnd_880979 := by exact prefixLift 880979
  have htrace : WordTrace (prefixWord ++ tailWord_880979) baseStart_880979 baseEnd_880979 := by
    simpa [prefixWord, tailWord_880979, baseEnd_880979] using wordTrace_append hprefix tailTrace_880979
  have hstable : (prefixWord ++ tailWord_880979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880979).length < 2 ^ (prefixWord ++ tailWord_880979).sum := by decide
  have hdescent : baseEnd_880979 < baseStart_880979 := by decide
  rcases family_descends (prefixWord ++ tailWord_880979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880993 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 8, 2, 2]
def baseStart_880993 : Nat := 118140960795 + 880993 * 2 ^ 59
def prefixEnd_880993 : Nat := 4983230072969 + 3 ^ 40 * 880993 * 2
def baseEnd_880993 : Nat := 452372862246576844535893

theorem tailTrace_880993 : CollatzResearch.WordTrace tailWord_880993 prefixEnd_880993 452372862246576844535893 := by
  unfold tailWord_880993
  simp only [CollatzResearch.WordTrace]
  refine ⟨32132454497320297470647633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21421636331546864980431755 32132454497320297470647633)
  ·
    refine ⟨24099340872990223102985725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32132454497320297470647633 24099340872990223102985725)
    ·
      refine ⟨9037252827371333663619647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24099340872990223102985725 9037252827371333663619647)
      ·
        refine ⟨13555879241057000495429471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9037252827371333663619647 13555879241057000495429471)
        ·
          refine ⟨20333818861585500743144207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13555879241057000495429471 20333818861585500743144207)
          ·
            refine ⟨30500728292378251114716311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20333818861585500743144207 30500728292378251114716311)
            ·
              refine ⟨45751092438567376672074467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30500728292378251114716311 45751092438567376672074467)
              ·
                refine ⟨68626638657851065008111701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45751092438567376672074467 68626638657851065008111701)
                ·
                  refine ⟨804218421771692168063809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 68626638657851065008111701 804218421771692168063809)
                  ·
                    refine ⟨603163816328769126047857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 804218421771692168063809 603163816328769126047857)
                    ·
                      refine ⟨452372862246576844535893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 603163816328769126047857 452372862246576844535893)
                      ·
                        rfl

theorem cell23_880993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 8, 2, 2].length) (baseStart_880993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_880993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_880993 prefixEnd_880993 := by exact prefixLift 880993
  have htrace : WordTrace (prefixWord ++ tailWord_880993) baseStart_880993 baseEnd_880993 := by
    simpa [prefixWord, tailWord_880993, baseEnd_880993] using wordTrace_append hprefix tailTrace_880993
  have hstable : (prefixWord ++ tailWord_880993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880993).length < 2 ^ (prefixWord ++ tailWord_880993).sum := by decide
  have hdescent : baseEnd_880993 < baseStart_880993 := by decide
  rcases family_descends (prefixWord ++ tailWord_880993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880996 : List Nat := [2, 3, 1, 1, 3, 1, 1, 2, 2, 4, 3]
def baseStart_880996 : Nat := 118140960795 + 880996 * 2 ^ 59
def prefixEnd_880996 : Nat := 4983230072969 + 3 ^ 40 * 880996 * 2
def baseEnd_880996 : Nat := 452374402688540332798379

theorem tailTrace_880996 : CollatzResearch.WordTrace tailWord_880996 prefixEnd_880996 452374402688540332798379 := by
  unfold tailWord_880996
  simp only [CollatzResearch.WordTrace]
  refine ⟨16066281958154714491503421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21421709277539619322004561 16066281958154714491503421)
  ·
    refine ⟨6024855734308017934313783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16066281958154714491503421 6024855734308017934313783)
    ·
      refine ⟨9037283601462026901470675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6024855734308017934313783 9037283601462026901470675)
      ·
        refine ⟨13555925402193040352206013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9037283601462026901470675 13555925402193040352206013)
        ·
          refine ⟨5083472025822390132077255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13555925402193040352206013 5083472025822390132077255)
          ·
            refine ⟨7625208038733585198115883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5083472025822390132077255 7625208038733585198115883)
            ·
              refine ⟨11437812058100377797173825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7625208038733585198115883 11437812058100377797173825)
              ·
                refine ⟨8578359043575283347880369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11437812058100377797173825 8578359043575283347880369)
                ·
                  refine ⟨6433769282681462510910277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8578359043575283347880369 6433769282681462510910277)
                  ·
                    refine ⟨1206331740502774220795677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6433769282681462510910277 1206331740502774220795677)
                    ·
                      refine ⟨452374402688540332798379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1206331740502774220795677 452374402688540332798379)
                      ·
                        rfl

theorem cell23_880996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 2, 4, 3].length) (baseStart_880996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_880996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_880996 prefixEnd_880996 := by exact prefixLift 880996
  have htrace : WordTrace (prefixWord ++ tailWord_880996) baseStart_880996 baseEnd_880996 := by
    simpa [prefixWord, tailWord_880996, baseEnd_880996] using wordTrace_append hprefix tailTrace_880996
  have hstable : (prefixWord ++ tailWord_880996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880996).length < 2 ^ (prefixWord ++ tailWord_880996).sum := by decide
  have hdescent : baseEnd_880996 < baseStart_880996 := by decide
  rcases family_descends (prefixWord ++ tailWord_880996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881009 : List Nat := [1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 7]
def baseStart_881009 : Nat := 118140960795 + 881009 * 2 ^ 59
def prefixEnd_881009 : Nat := 4983230072969 + 3 ^ 40 * 881009 * 2
def baseEnd_881009 : Nat := 452381077937048781935819

theorem tailTrace_881009 : CollatzResearch.WordTrace tailWord_881009 prefixEnd_881009 452381077937048781935819 := by
  unfold tailWord_881009
  simp only [CollatzResearch.WordTrace]
  refine ⟨32133038065262332203230081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21422025376841554802153387 32133038065262332203230081)
  ·
    refine ⟨24099778548946749152422561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32133038065262332203230081 24099778548946749152422561)
    ·
      refine ⟨18074833911710061864316921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24099778548946749152422561 18074833911710061864316921)
      ·
        refine ⟨13556125433782546398237691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18074833911710061864316921 13556125433782546398237691)
        ·
          refine ⟨20334188150673819597356537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13556125433782546398237691 20334188150673819597356537)
          ·
            refine ⟨15250641113005364698017403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20334188150673819597356537 15250641113005364698017403)
            ·
              refine ⟨22875961669508047047026105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15250641113005364698017403 22875961669508047047026105)
              ·
                refine ⟨17156971252131035285269579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22875961669508047047026105 17156971252131035285269579)
                ·
                  refine ⟨25735456878196552927904369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17156971252131035285269579 25735456878196552927904369)
                  ·
                    refine ⟨19301592658647414695928277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25735456878196552927904369 19301592658647414695928277)
                    ·
                      refine ⟨452381077937048781935819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 19301592658647414695928277 452381077937048781935819)
                      ·
                        rfl

theorem cell23_881009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_881009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_881009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_881009 prefixEnd_881009 := by exact prefixLift 881009
  have htrace : WordTrace (prefixWord ++ tailWord_881009) baseStart_881009 baseEnd_881009 := by
    simpa [prefixWord, tailWord_881009, baseEnd_881009] using wordTrace_append hprefix tailTrace_881009
  have hstable : (prefixWord ++ tailWord_881009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881009).length < 2 ^ (prefixWord ++ tailWord_881009).sum := by decide
  have hdescent : baseEnd_881009 < baseStart_881009 := by decide
  rcases family_descends (prefixWord ++ tailWord_881009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881014 : List Nat := [5, 1, 1, 4, 1, 1, 1, 3, 1, 3, 2]
def baseStart_881014 : Nat := 118140960795 + 881014 * 2 ^ 59
def prefixEnd_881014 : Nat := 4983230072969 + 3 ^ 40 * 881014 * 2
def baseEnd_881014 : Nat := 452383645340321262373297

theorem tailTrace_881014 : CollatzResearch.WordTrace tailWord_881014 prefixEnd_881014 452383645340321262373297 := by
  unfold tailWord_881014
  simp only [CollatzResearch.WordTrace]
  refine ⟨2008326276890263628572631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21422146953496145371441397 2008326276890263628572631)
  ·
    refine ⟨3012489415335395442858947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2008326276890263628572631 3012489415335395442858947)
    ·
      refine ⟨4518734123003093164288421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3012489415335395442858947 4518734123003093164288421)
      ·
        refine ⟨847262648063079968304079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4518734123003093164288421 847262648063079968304079)
        ·
          refine ⟨1270893972094619952456119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 847262648063079968304079 1270893972094619952456119)
          ·
            refine ⟨1906340958141929928684179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1270893972094619952456119 1906340958141929928684179)
            ·
              refine ⟨2859511437212894893026269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1906340958141929928684179 2859511437212894893026269)
              ·
                refine ⟨1072316788954835584884851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2859511437212894893026269 1072316788954835584884851)
                ·
                  refine ⟨1608475183432253377327277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1072316788954835584884851 1608475183432253377327277)
                  ·
                    refine ⟨603178193787095016497729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1608475183432253377327277 603178193787095016497729)
                    ·
                      refine ⟨452383645340321262373297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 603178193787095016497729 452383645340321262373297)
                      ·
                        rfl

theorem cell23_881014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_881014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_881014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_881014 prefixEnd_881014 := by exact prefixLift 881014
  have htrace : WordTrace (prefixWord ++ tailWord_881014) baseStart_881014 baseEnd_881014 := by
    simpa [prefixWord, tailWord_881014, baseEnd_881014] using wordTrace_append hprefix tailTrace_881014
  have hstable : (prefixWord ++ tailWord_881014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881014).length < 2 ^ (prefixWord ++ tailWord_881014).sum := by decide
  have hdescent : baseEnd_881014 < baseStart_881014 := by decide
  rcases family_descends (prefixWord ++ tailWord_881014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881033 : List Nat := [1, 2, 1, 1, 6, 1, 2, 4, 5]
def baseStart_881033 : Nat := 118140960795 + 881033 * 2 ^ 59
def prefixEnd_881033 : Nat := 4983230072969 + 3 ^ 40 * 881033 * 2
def baseEnd_881033 : Nat := 50265933496972965337301

theorem tailTrace_881033 : CollatzResearch.WordTrace tailWord_881033 prefixEnd_881033 50265933496972965337301 := by
  unfold tailWord_881033
  simp only [CollatzResearch.WordTrace]
  refine ⟨32133913417175384302103753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21422608944783589534735835 32133913417175384302103753)
  ·
    refine ⟨24100435062881538226577815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32133913417175384302103753 24100435062881538226577815)
    ·
      refine ⟨36150652594322307339866723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24100435062881538226577815 36150652594322307339866723)
      ·
        refine ⟨54225978891483461009800085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36150652594322307339866723 54225978891483461009800085)
        ·
          refine ⟨2541842760538287234834379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 54225978891483461009800085 2541842760538287234834379)
          ·
            refine ⟨3812764140807430852251569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2541842760538287234834379 3812764140807430852251569)
            ·
              refine ⟨2859573105605573139188677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3812764140807430852251569 2859573105605573139188677)
              ·
                refine ⟨536169957301044963597877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2859573105605573139188677 536169957301044963597877)
                ·
                  refine ⟨50265933496972965337301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 536169957301044963597877 50265933496972965337301)
                  ·
                    rfl

theorem cell23_881033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 4, 5].length) (baseStart_881033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_881033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_881033 prefixEnd_881033 := by exact prefixLift 881033
  have htrace : WordTrace (prefixWord ++ tailWord_881033) baseStart_881033 baseEnd_881033 := by
    simpa [prefixWord, tailWord_881033, baseEnd_881033] using wordTrace_append hprefix tailTrace_881033
  have hstable : (prefixWord ++ tailWord_881033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881033).length < 2 ^ (prefixWord ++ tailWord_881033).sum := by decide
  have hdescent : baseEnd_881033 < baseStart_881033 := by decide
  rcases family_descends (prefixWord ++ tailWord_881033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881044 : List Nat := [2, 4, 2, 1, 4, 1, 1, 1, 1, 4, 2]
def baseStart_881044 : Nat := 118140960795 + 881044 * 2 ^ 59
def prefixEnd_881044 : Nat := 4983230072969 + 3 ^ 40 * 881044 * 2
def baseEnd_881044 : Nat := 452399049759956144998159

theorem tailTrace_881044 : CollatzResearch.WordTrace tailWord_881044 prefixEnd_881044 452399049759956144998159 := by
  unfold tailWord_881044
  simp only [CollatzResearch.WordTrace]
  refine ⟨16067157310067766590377093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21422876413423688787169457 16067157310067766590377093)
  ·
    refine ⟨3012591995637706235695705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16067157310067766590377093 3012591995637706235695705)
    ·
      refine ⟨2259443996728279676771779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3012591995637706235695705 2259443996728279676771779)
      ·
        refine ⟨3389165995092419515157669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2259443996728279676771779 3389165995092419515157669)
        ·
          refine ⟨635468624079828659092063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3389165995092419515157669 635468624079828659092063)
          ·
            refine ⟨953202936119742988638095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 635468624079828659092063 953202936119742988638095)
            ·
              refine ⟨1429804404179614482957143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 953202936119742988638095 1429804404179614482957143)
              ·
                refine ⟨2144706606269421724435715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1429804404179614482957143 2144706606269421724435715)
                ·
                  refine ⟨3217059909404132586653573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2144706606269421724435715 3217059909404132586653573)
                  ·
                    refine ⟨603198733013274859997545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3217059909404132586653573 603198733013274859997545)
                    ·
                      refine ⟨452399049759956144998159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 603198733013274859997545 452399049759956144998159)
                      ·
                        rfl

theorem cell23_881044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_881044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_881044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_881044 prefixEnd_881044 := by exact prefixLift 881044
  have htrace : WordTrace (prefixWord ++ tailWord_881044) baseStart_881044 baseEnd_881044 := by
    simpa [prefixWord, tailWord_881044, baseEnd_881044] using wordTrace_append hprefix tailTrace_881044
  have hstable : (prefixWord ++ tailWord_881044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881044).length < 2 ^ (prefixWord ++ tailWord_881044).sum := by decide
  have hdescent : baseEnd_881044 < baseStart_881044 := by decide
  rcases family_descends (prefixWord ++ tailWord_881044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881110 : List Nat := [5, 2, 1, 1, 1, 1, 2, 1, 5, 4]
def baseStart_881110 : Nat := 118140960795 + 881110 * 2 ^ 59
def prefixEnd_881110 : Nat := 4983230072969 + 3 ^ 40 * 881110 * 2
def baseEnd_881110 : Nat := 150810979827717628924285

theorem tailTrace_881110 : CollatzResearch.WordTrace tailWord_881110 prefixEnd_881110 150810979827717628924285 := by
  unfold tailWord_881110
  simp only [CollatzResearch.WordTrace]
  refine ⟨2008545114868526653291049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21424481225264284301771189 2008545114868526653291049)
  ·
    refine ⟨1506408836151394989968287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2008545114868526653291049 1506408836151394989968287)
    ·
      refine ⟨2259613254227092484952431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1506408836151394989968287 2259613254227092484952431)
      ·
        refine ⟨3389419881340638727428647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2259613254227092484952431 3389419881340638727428647)
        ·
          refine ⟨5084129822010958091142971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3389419881340638727428647 5084129822010958091142971)
          ·
            refine ⟨7626194733016437136714457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5084129822010958091142971 7626194733016437136714457)
            ·
              refine ⟨5719646049762327852535843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7626194733016437136714457 5719646049762327852535843)
              ·
                refine ⟨8579469074643491778803765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5719646049762327852535843 8579469074643491778803765)
                ·
                  refine ⟨804325225747827354262853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8579469074643491778803765 804325225747827354262853)
                  ·
                    refine ⟨150810979827717628924285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 804325225747827354262853 150810979827717628924285)
                    ·
                      rfl

theorem cell23_881110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_881110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_881110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_881110 prefixEnd_881110 := by exact prefixLift 881110
  have htrace : WordTrace (prefixWord ++ tailWord_881110) baseStart_881110 baseEnd_881110 := by
    simpa [prefixWord, tailWord_881110, baseEnd_881110] using wordTrace_append hprefix tailTrace_881110
  have hstable : (prefixWord ++ tailWord_881110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881110).length < 2 ^ (prefixWord ++ tailWord_881110).sum := by decide
  have hdescent : baseEnd_881110 < baseStart_881110 := by decide
  rcases family_descends (prefixWord ++ tailWord_881110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881153 : List Nat := [1, 2, 4, 1, 3, 1, 1, 2, 3, 5]
def baseStart_881153 : Nat := 118140960795 + 881153 * 2 ^ 59
def prefixEnd_881153 : Nat := 4983230072969 + 3 ^ 40 * 881153 * 2
def baseEnd_881153 : Nat := 150818339717098739511719

theorem tailTrace_881153 : CollatzResearch.WordTrace tailWord_881153 prefixEnd_881153 150818339717098739511719 := by
  unfold tailWord_881153
  simp only [CollatzResearch.WordTrace]
  refine ⟨32138290176740644796472113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21425526784493763197648075 32138290176740644796472113)
  ·
    refine ⟨24103717632555483597354085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32138290176740644796472113 24103717632555483597354085)
    ·
      refine ⟨4519447056104153174503891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24103717632555483597354085 4519447056104153174503891)
      ·
        refine ⟨6779170584156229761755837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4519447056104153174503891 6779170584156229761755837)
        ·
          refine ⟨2542188969058586160658439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6779170584156229761755837 2542188969058586160658439)
          ·
            refine ⟨3813283453587879240987659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2542188969058586160658439 3813283453587879240987659)
            ·
              refine ⟨5719925180381818861481489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3813283453587879240987659 5719925180381818861481489)
              ·
                refine ⟨4289943885286364146111117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5719925180381818861481489 4289943885286364146111117)
                ·
                  refine ⟨1608728956982386554791669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4289943885286364146111117 1608728956982386554791669)
                  ·
                    refine ⟨150818339717098739511719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1608728956982386554791669 150818339717098739511719)
                    ·
                      rfl

theorem cell23_881153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_881153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_881153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_881153 prefixEnd_881153 := by exact prefixLift 881153
  have htrace : WordTrace (prefixWord ++ tailWord_881153) baseStart_881153 baseEnd_881153 := by
    simpa [prefixWord, tailWord_881153, baseEnd_881153] using wordTrace_append hprefix tailTrace_881153
  have hstable : (prefixWord ++ tailWord_881153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881153).length < 2 ^ (prefixWord ++ tailWord_881153).sum := by decide
  have hdescent : baseEnd_881153 < baseStart_881153 := by decide
  rcases family_descends (prefixWord ++ tailWord_881153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881173 : List Nat := [1, 3, 2, 1, 3, 1, 1, 3, 3, 1, 4]
def baseStart_881173 : Nat := 118140960795 + 881173 * 2 ^ 59
def prefixEnd_881173 : Nat := 4983230072969 + 3 ^ 40 * 881173 * 2
def baseEnd_881173 : Nat := 452465288764386140285065

theorem tailTrace_881173 : CollatzResearch.WordTrace tailWord_881173 prefixEnd_881173 452465288764386140285065 := by
  unfold tailWord_881173
  simp only [CollatzResearch.WordTrace]
  refine ⟨32139019636668188212200173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21426013091112125474800115 32139019636668188212200173)
  ·
    refine ⟨12052132363750570579575065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32139019636668188212200173 12052132363750570579575065)
    ·
      refine ⟨9039099272812927934681299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12052132363750570579575065 9039099272812927934681299)
      ·
        refine ⟨13558648909219391902021949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9039099272812927934681299 13558648909219391902021949)
        ·
          refine ⟨5084493340957271963258231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13558648909219391902021949 5084493340957271963258231)
          ·
            refine ⟨7626740011435907944887347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5084493340957271963258231 7626740011435907944887347)
            ·
              refine ⟨11440110017153861917331021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7626740011435907944887347 11440110017153861917331021)
              ·
                refine ⟨4290041256432698218999133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11440110017153861917331021 4290041256432698218999133)
                ·
                  refine ⟨1608765471162261832124675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4290041256432698218999133 1608765471162261832124675)
                  ·
                    refine ⟨2413148206743392748187013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1608765471162261832124675 2413148206743392748187013)
                    ·
                      refine ⟨452465288764386140285065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2413148206743392748187013 452465288764386140285065)
                      ·
                        rfl

theorem cell23_881173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 3, 1, 4].length) (baseStart_881173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_881173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_881173 prefixEnd_881173 := by exact prefixLift 881173
  have htrace : WordTrace (prefixWord ++ tailWord_881173) baseStart_881173 baseEnd_881173 := by
    simpa [prefixWord, tailWord_881173, baseEnd_881173] using wordTrace_append hprefix tailTrace_881173
  have hstable : (prefixWord ++ tailWord_881173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881173).length < 2 ^ (prefixWord ++ tailWord_881173).sum := by decide
  have hdescent : baseEnd_881173 < baseStart_881173 := by decide
  rcases family_descends (prefixWord ++ tailWord_881173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881183 : List Nat := [1, 1, 2, 4, 1, 1, 1, 4, 4, 4]
def baseStart_881183 : Nat := 118140960795 + 881183 * 2 ^ 59
def prefixEnd_881183 : Nat := 4983230072969 + 3 ^ 40 * 881183 * 2
def baseEnd_881183 : Nat := 150823474523643700386673

theorem tailTrace_881183 : CollatzResearch.WordTrace tailWord_881183 prefixEnd_881183 150823474523643700386673 := by
  unfold tailWord_881183
  simp only [CollatzResearch.WordTrace]
  refine ⟨32139384366631959920064203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21426256244421306613376135 32139384366631959920064203)
  ·
    refine ⟨48209076549947939880096305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32139384366631959920064203 48209076549947939880096305)
    ·
      refine ⟨36156807412460954910072229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48209076549947939880096305 36156807412460954910072229)
      ·
        refine ⟨6779401389836429045638543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36156807412460954910072229 6779401389836429045638543)
        ·
          refine ⟨10169102084754643568457815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6779401389836429045638543 10169102084754643568457815)
          ·
            refine ⟨15253653127131965352686723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10169102084754643568457815 15253653127131965352686723)
            ·
              refine ⟨22880479690697948029030085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15253653127131965352686723 22880479690697948029030085)
              ·
                refine ⟨4290089942005865255443141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22880479690697948029030085 4290089942005865255443141)
                ·
                  refine ⟨804391864126099735395589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4290089942005865255443141 804391864126099735395589)
                  ·
                    refine ⟨150823474523643700386673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 804391864126099735395589 150823474523643700386673)
                    ·
                      rfl

theorem cell23_881183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 4, 4].length) (baseStart_881183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_881183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_881183 prefixEnd_881183 := by exact prefixLift 881183
  have htrace : WordTrace (prefixWord ++ tailWord_881183) baseStart_881183 baseEnd_881183 := by
    simpa [prefixWord, tailWord_881183, baseEnd_881183] using wordTrace_append hprefix tailTrace_881183
  have hstable : (prefixWord ++ tailWord_881183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881183).length < 2 ^ (prefixWord ++ tailWord_881183).sum := by decide
  have hdescent : baseEnd_881183 < baseStart_881183 := by decide
  rcases family_descends (prefixWord ++ tailWord_881183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881187 : List Nat := [1, 1, 1, 4, 4, 3, 2, 1, 1, 5]
def baseStart_881187 : Nat := 118140960795 + 881187 * 2 ^ 59
def prefixEnd_881187 : Nat := 4983230072969 + 3 ^ 40 * 881187 * 2
def baseEnd_881187 : Nat := 150824159164516361836667

theorem tailTrace_881187 : CollatzResearch.WordTrace tailWord_881187 prefixEnd_881187 150824159164516361836667 := by
  unfold tailWord_881187
  simp only [CollatzResearch.WordTrace]
  refine ⟨32139530258617468603209815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21426353505744979068806543 32139530258617468603209815)
  ·
    refine ⟨48209295387926202904814723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32139530258617468603209815 48209295387926202904814723)
    ·
      refine ⟨72313943081889304357222085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48209295387926202904814723 72313943081889304357222085)
      ·
        refine ⟨13558864327854244566979141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72313943081889304357222085 13558864327854244566979141)
        ·
          refine ⟨2542287061472670856308589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13558864327854244566979141 2542287061472670856308589)
          ·
            refine ⟨953357648052251571115721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2542287061472670856308589 953357648052251571115721)
            ·
              refine ⟨715018236039188678336791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 953357648052251571115721 715018236039188678336791)
              ·
                refine ⟨1072527354058783017505187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 715018236039188678336791 1072527354058783017505187)
                ·
                  refine ⟨1608791031088174526257781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1072527354058783017505187 1608791031088174526257781)
                  ·
                    refine ⟨150824159164516361836667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1608791031088174526257781 150824159164516361836667)
                    ·
                      rfl

theorem cell23_881187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 2, 1, 1, 5].length) (baseStart_881187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_881187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_881187 prefixEnd_881187 := by exact prefixLift 881187
  have htrace : WordTrace (prefixWord ++ tailWord_881187) baseStart_881187 baseEnd_881187 := by
    simpa [prefixWord, tailWord_881187, baseEnd_881187] using wordTrace_append hprefix tailTrace_881187
  have hstable : (prefixWord ++ tailWord_881187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881187).length < 2 ^ (prefixWord ++ tailWord_881187).sum := by decide
  have hdescent : baseEnd_881187 < baseStart_881187 := by decide
  rcases family_descends (prefixWord ++ tailWord_881187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881200 : List Nat := [2, 1, 1, 1, 2, 3, 5, 2, 2, 4]
def baseStart_881200 : Nat := 118140960795 + 881200 * 2 ^ 59
def prefixEnd_881200 : Nat := 4983230072969 + 3 ^ 40 * 881200 * 2
def baseEnd_881200 : Nat := 150826384247352511549147

theorem tailTrace_881200 : CollatzResearch.WordTrace tailWord_881200 prefixEnd_881200 150826384247352511549147 := by
  unfold tailWord_881200
  simp only [CollatzResearch.WordTrace]
  refine ⟨16070002203785185911716527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21426669605046914548955369 16070002203785185911716527)
  ·
    refine ⟨24105003305677778867574791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16070002203785185911716527 24105003305677778867574791)
    ·
      refine ⟨36157504958516668301362187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24105003305677778867574791 36157504958516668301362187)
      ·
        refine ⟨54236257437775002452043281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36157504958516668301362187 54236257437775002452043281)
        ·
          refine ⟨40677193078331251839032461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54236257437775002452043281 40677193078331251839032461)
          ·
            refine ⟨15253947404374219439637173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40677193078331251839032461 15253947404374219439637173)
            ·
              refine ⟨1430057569160083072465985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15253947404374219439637173 1430057569160083072465985)
              ·
                refine ⟨1072543176870062304349489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1430057569160083072465985 1072543176870062304349489)
                ·
                  refine ⟨804407382652546728262117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1072543176870062304349489 804407382652546728262117)
                  ·
                    refine ⟨150826384247352511549147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 804407382652546728262117 150826384247352511549147)
                    ·
                      rfl

theorem cell23_881200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 2, 2, 4].length) (baseStart_881200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_881200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_881200 prefixEnd_881200 := by exact prefixLift 881200
  have htrace : WordTrace (prefixWord ++ tailWord_881200) baseStart_881200 baseEnd_881200 := by
    simpa [prefixWord, tailWord_881200, baseEnd_881200] using wordTrace_append hprefix tailTrace_881200
  have hstable : (prefixWord ++ tailWord_881200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881200).length < 2 ^ (prefixWord ++ tailWord_881200).sum := by decide
  have hdescent : baseEnd_881200 < baseStart_881200 := by decide
  rcases family_descends (prefixWord ++ tailWord_881200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881207 : List Nat := [1, 1, 3, 1, 2, 3, 4, 1, 3, 2, 2]
def baseStart_881207 : Nat := 118140960795 + 881207 * 2 ^ 59
def prefixEnd_881207 : Nat := 4983230072969 + 3 ^ 40 * 881207 * 2
def baseEnd_881207 : Nat := 452482747106639007259909

theorem tailTrace_881207 : CollatzResearch.WordTrace tailWord_881207 prefixEnd_881207 452482747106639007259909 := by
  unfold tailWord_881207
  simp only [CollatzResearch.WordTrace]
  refine ⟨32140259718545012018937875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21426839812363341345958583 32140259718545012018937875)
  ·
    refine ⟨48210389577817518028406813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32140259718545012018937875 48210389577817518028406813)
    ·
      refine ⟨18078896091681569260652555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48210389577817518028406813 18078896091681569260652555)
      ·
        refine ⟨27118344137522353890978833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18078896091681569260652555 27118344137522353890978833)
        ·
          refine ⟨20338758103141765418234125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27118344137522353890978833 20338758103141765418234125)
          ·
            refine ⟨7627034288678162031837797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20338758103141765418234125 7627034288678162031837797)
            ·
              refine ⟨1430068929127155380969587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7627034288678162031837797 1430068929127155380969587)
              ·
                refine ⟨2145103393690733071454381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1430068929127155380969587 2145103393690733071454381)
                ·
                  refine ⟨804413772634024901795393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2145103393690733071454381 804413772634024901795393)
                  ·
                    refine ⟨603310329475518676346545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 804413772634024901795393 603310329475518676346545)
                    ·
                      refine ⟨452482747106639007259909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 603310329475518676346545 452482747106639007259909)
                      ·
                        rfl

theorem cell23_881207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 1, 3, 2, 2].length) (baseStart_881207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_881207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_881207 prefixEnd_881207 := by exact prefixLift 881207
  have htrace : WordTrace (prefixWord ++ tailWord_881207) baseStart_881207 baseEnd_881207 := by
    simpa [prefixWord, tailWord_881207, baseEnd_881207] using wordTrace_append hprefix tailTrace_881207
  have hstable : (prefixWord ++ tailWord_881207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881207).length < 2 ^ (prefixWord ++ tailWord_881207).sum := by decide
  have hdescent : baseEnd_881207 < baseStart_881207 := by decide
  rcases family_descends (prefixWord ++ tailWord_881207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881240 : List Nat := [2, 1, 2, 2, 1, 2, 3, 2, 4, 1, 3]
def baseStart_881240 : Nat := 118140960795 + 881240 * 2 ^ 59
def prefixEnd_881240 : Nat := 4983230072969 + 3 ^ 40 * 881240 * 2
def baseEnd_881240 : Nat := 452499691968237378147257

theorem tailTrace_881240 : CollatzResearch.WordTrace tailWord_881240 prefixEnd_881240 452499691968237378147257 := by
  unfold tailWord_881240
  simp only [CollatzResearch.WordTrace]
  refine ⟨16070731663712729327444587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21427642218283639103259449 16070731663712729327444587)
  ·
    refine ⟨24106097495569093991166881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16070731663712729327444587 24106097495569093991166881)
    ·
      refine ⟨18079573121676820493375161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24106097495569093991166881 18079573121676820493375161)
      ·
        refine ⟨13559679841257615370031371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18079573121676820493375161 13559679841257615370031371)
        ·
          refine ⟨20339519761886423055047057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13559679841257615370031371 20339519761886423055047057)
          ·
            refine ⟨15254639821414817291285293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20339519761886423055047057 15254639821414817291285293)
            ·
              refine ⟨5720489933030556484231985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15254639821414817291285293 5720489933030556484231985)
              ·
                refine ⟨4290367449772917363173989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5720489933030556484231985 4290367449772917363173989)
                ·
                  refine ⟨804443896832422005595123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4290367449772917363173989 804443896832422005595123)
                  ·
                    refine ⟨1206665845248633008392685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 804443896832422005595123 1206665845248633008392685)
                    ·
                      refine ⟨452499691968237378147257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1206665845248633008392685 452499691968237378147257)
                      ·
                        rfl

theorem cell23_881240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 4, 1, 3].length) (baseStart_881240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_881240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_881240 prefixEnd_881240 := by exact prefixLift 881240
  have htrace : WordTrace (prefixWord ++ tailWord_881240) baseStart_881240 baseEnd_881240 := by
    simpa [prefixWord, tailWord_881240, baseEnd_881240] using wordTrace_append hprefix tailTrace_881240
  have hstable : (prefixWord ++ tailWord_881240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881240).length < 2 ^ (prefixWord ++ tailWord_881240).sum := by decide
  have hdescent : baseEnd_881240 < baseStart_881240 := by decide
  rcases family_descends (prefixWord ++ tailWord_881240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881283 : List Nat := [1, 1, 1, 3, 3, 1, 3, 2, 2, 1, 5]
def baseStart_881283 : Nat := 118140960795 + 881283 * 2 ^ 59
def prefixEnd_881283 : Nat := 4983230072969 + 3 ^ 40 * 881283 * 2
def baseEnd_881283 : Nat := 452521771636380709909559

theorem tailTrace_881283 : CollatzResearch.WordTrace tailWord_881283 prefixEnd_881283 452521771636380709909559 := by
  unfold tailWord_881283
  simp only [CollatzResearch.WordTrace]
  refine ⟨32143031666269676998704503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21428687777513117999136335 32143031666269676998704503)
  ·
    refine ⟨48214547499404515498056755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32143031666269676998704503 48214547499404515498056755)
    ·
      refine ⟨72321821249106773247085133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48214547499404515498056755 72321821249106773247085133)
      ·
        refine ⟨27120682968415039967656925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72321821249106773247085133 27120682968415039967656925)
        ·
          refine ⟨10170256113155639987871347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27120682968415039967656925 10170256113155639987871347)
          ·
            refine ⟨15255384169733459981807021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10170256113155639987871347 15255384169733459981807021)
            ·
              refine ⟨5720769063650047493177633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15255384169733459981807021 5720769063650047493177633)
              ·
                refine ⟨4290576797737535619883225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5720769063650047493177633 4290576797737535619883225)
                ·
                  refine ⟨3217932598303151714912419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4290576797737535619883225 3217932598303151714912419)
                  ·
                    refine ⟨4826898897454727572368629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3217932598303151714912419 4826898897454727572368629)
                    ·
                      refine ⟨452521771636380709909559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4826898897454727572368629 452521771636380709909559)
                      ·
                        rfl

theorem cell23_881283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 2, 1, 5].length) (baseStart_881283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_881283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_881283 prefixEnd_881283 := by exact prefixLift 881283
  have htrace : WordTrace (prefixWord ++ tailWord_881283) baseStart_881283 baseEnd_881283 := by
    simpa [prefixWord, tailWord_881283, baseEnd_881283] using wordTrace_append hprefix tailTrace_881283
  have hstable : (prefixWord ++ tailWord_881283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881283).length < 2 ^ (prefixWord ++ tailWord_881283).sum := by decide
  have hdescent : baseEnd_881283 < baseStart_881283 := by decide
  rcases family_descends (prefixWord ++ tailWord_881283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881284 : List Nat := [2, 3, 2, 1, 3, 1, 3, 2, 1, 3, 2]
def baseStart_881284 : Nat := 118140960795 + 881284 * 2 ^ 59
def prefixEnd_881284 : Nat := 4983230072969 + 3 ^ 40 * 881284 * 2
def baseEnd_881284 : Nat := 452522285117035205997055

theorem tailTrace_881284 : CollatzResearch.WordTrace tailWord_881284 prefixEnd_881284 452522285117035205997055 := by
  unfold tailWord_881284
  simp only [CollatzResearch.WordTrace]
  refine ⟨16071534069633027084745453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21428712092844036112993937 16071534069633027084745453)
  ·
    refine ⟨6026825276112385156779545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16071534069633027084745453 6026825276112385156779545)
    ·
      refine ⟨4520118957084288867584659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6026825276112385156779545 4520118957084288867584659)
      ·
        refine ⟨6780178435626433301376989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4520118957084288867584659 6780178435626433301376989)
        ·
          refine ⟨2542566913359912488016371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6780178435626433301376989 2542566913359912488016371)
          ·
            refine ⟨3813850370039868732024557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2542566913359912488016371 3813850370039868732024557)
            ·
              refine ⟨1430193888764950774509209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3813850370039868732024557 1430193888764950774509209)
              ·
                refine ⟨1072645416573713080881907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1430193888764950774509209 1072645416573713080881907)
                ·
                  refine ⟨1608968124860569621322861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1072645416573713080881907 1608968124860569621322861)
                  ·
                    refine ⟨603363046822713607996073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1608968124860569621322861 603363046822713607996073)
                    ·
                      refine ⟨452522285117035205997055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 603363046822713607996073 452522285117035205997055)
                      ·
                        rfl

theorem cell23_881284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 2, 1, 3, 2].length) (baseStart_881284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_881284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_881284 prefixEnd_881284 := by exact prefixLift 881284
  have htrace : WordTrace (prefixWord ++ tailWord_881284) baseStart_881284 baseEnd_881284 := by
    simpa [prefixWord, tailWord_881284, baseEnd_881284] using wordTrace_append hprefix tailTrace_881284
  have hstable : (prefixWord ++ tailWord_881284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881284).length < 2 ^ (prefixWord ++ tailWord_881284).sum := by decide
  have hdescent : baseEnd_881284 < baseStart_881284 := by decide
  rcases family_descends (prefixWord ++ tailWord_881284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881365 : List Nat := [1, 3, 2, 5, 2, 1, 1, 2, 2, 2, 2]
def baseStart_881365 : Nat := 118140960795 + 881365 * 2 ^ 59
def prefixEnd_881365 : Nat := 4983230072969 + 3 ^ 40 * 881365 * 2
def baseEnd_881365 : Nat := 452563877050049389084183

theorem tailTrace_881365 : CollatzResearch.WordTrace tailWord_881365 prefixEnd_881365 452563877050049389084183 := by
  unfold tailWord_881365
  simp only [CollatzResearch.WordTrace]
  refine ⟨32146022451972605003189549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21430681634648403335459699 32146022451972605003189549)
  ·
    refine ⟨12054758419489726876196081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32146022451972605003189549 12054758419489726876196081)
    ·
      refine ⟨9041068814617295157147061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12054758419489726876196081 9041068814617295157147061)
      ·
        refine ⟨847600201370371420982537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9041068814617295157147061 847600201370371420982537)
        ·
          refine ⟨635700151027778565736903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 847600201370371420982537 635700151027778565736903)
          ·
            refine ⟨953550226541667848605355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 635700151027778565736903 953550226541667848605355)
            ·
              refine ⟨1430325339812501772908033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 953550226541667848605355 1430325339812501772908033)
              ·
                refine ⟨1072744004859376329681025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1430325339812501772908033 1072744004859376329681025)
                ·
                  refine ⟨804558003644532247260769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1072744004859376329681025 804558003644532247260769)
                  ·
                    refine ⟨603418502733399185445577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 804558003644532247260769 603418502733399185445577)
                    ·
                      refine ⟨452563877050049389084183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 603418502733399185445577 452563877050049389084183)
                      ·
                        rfl

theorem cell23_881365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_881365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_881365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_881365 prefixEnd_881365 := by exact prefixLift 881365
  have htrace : WordTrace (prefixWord ++ tailWord_881365) baseStart_881365 baseEnd_881365 := by
    simpa [prefixWord, tailWord_881365, baseEnd_881365] using wordTrace_append hprefix tailTrace_881365
  have hstable : (prefixWord ++ tailWord_881365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881365).length < 2 ^ (prefixWord ++ tailWord_881365).sum := by decide
  have hdescent : baseEnd_881365 < baseStart_881365 := by decide
  rcases family_descends (prefixWord ++ tailWord_881365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881370 : List Nat := [3, 1, 1, 2, 2, 2, 2, 1, 4, 1, 4]
def baseStart_881370 : Nat := 118140960795 + 881370 * 2 ^ 59
def prefixEnd_881370 : Nat := 4983230072969 + 3 ^ 40 * 881370 * 2
def baseEnd_881370 : Nat := 452566444453321869521659

theorem tailTrace_881370 : CollatzResearch.WordTrace tailWord_881370 prefixEnd_881370 452566444453321869521659 := by
  unfold tailWord_881370
  simp only [CollatzResearch.WordTrace]
  refine ⟨8036551204238622714280391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21430803211302993904747709 8036551204238622714280391)
  ·
    refine ⟨12054826806357934071420587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8036551204238622714280391 12054826806357934071420587)
    ·
      refine ⟨18082240209536901107130881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12054826806357934071420587 18082240209536901107130881)
      ·
        refine ⟨13561680157152675830348161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18082240209536901107130881 13561680157152675830348161)
        ·
          refine ⟨10171260117864506872761121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13561680157152675830348161 10171260117864506872761121)
          ·
            refine ⟨7628445088398380154570841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10171260117864506872761121 7628445088398380154570841)
            ·
              refine ⟨5721333816298785115928131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7628445088398380154570841 5721333816298785115928131)
              ·
                refine ⟨8582000724448177673892197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5721333816298785115928131 8582000724448177673892197)
                ·
                  refine ⟨1609125135834033313854787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8582000724448177673892197 1609125135834033313854787)
                  ·
                    refine ⟨2413687703751049970782181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1609125135834033313854787 2413687703751049970782181)
                    ·
                      refine ⟨452566444453321869521659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2413687703751049970782181 452566444453321869521659)
                      ·
                        rfl

theorem cell23_881370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 4, 1, 4].length) (baseStart_881370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_881370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_881370 prefixEnd_881370 := by exact prefixLift 881370
  have htrace : WordTrace (prefixWord ++ tailWord_881370) baseStart_881370 baseEnd_881370 := by
    simpa [prefixWord, tailWord_881370, baseEnd_881370] using wordTrace_append hprefix tailTrace_881370
  have hstable : (prefixWord ++ tailWord_881370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881370).length < 2 ^ (prefixWord ++ tailWord_881370).sum := by decide
  have hdescent : baseEnd_881370 < baseStart_881370 := by decide
  rcases family_descends (prefixWord ++ tailWord_881370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881431 : List Nat := [1, 1, 3, 4, 4, 1, 1, 1, 3, 4]
def baseStart_881431 : Nat := 118140960795 + 881431 * 2 ^ 59
def prefixEnd_881431 : Nat := 4983230072969 + 3 ^ 40 * 881431 * 2
def baseEnd_881431 : Nat := 150865922257748710286293

theorem tailTrace_881431 : CollatzResearch.WordTrace tailWord_881431 prefixEnd_881431 150865922257748710286293 := by
  unfold tailWord_881431
  simp only [CollatzResearch.WordTrace]
  refine ⟨32148429669733498275092147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21432286446488998850061431 32148429669733498275092147)
  ·
    refine ⟨48222644504600247412638221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32148429669733498275092147 48222644504600247412638221)
    ·
      refine ⟨18083491689225092779739333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48222644504600247412638221 18083491689225092779739333)
      ·
        refine ⟨3390654691729704896201125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18083491689225092779739333 3390654691729704896201125)
        ·
          refine ⟨635747754699319668037711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3390654691729704896201125 635747754699319668037711)
          ·
            refine ⟨953621632048979502056567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 635747754699319668037711 953621632048979502056567)
            ·
              refine ⟨1430432448073469253084851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 953621632048979502056567 1430432448073469253084851)
              ·
                refine ⟨2145648672110203879627277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1430432448073469253084851 2145648672110203879627277)
                ·
                  refine ⟨804618252041326454860229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2145648672110203879627277 804618252041326454860229)
                  ·
                    refine ⟨150865922257748710286293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 804618252041326454860229 150865922257748710286293)
                    ·
                      rfl

theorem cell23_881431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 1, 3, 4].length) (baseStart_881431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_881431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_881431 prefixEnd_881431 := by exact prefixLift 881431
  have htrace : WordTrace (prefixWord ++ tailWord_881431) baseStart_881431 baseEnd_881431 := by
    simpa [prefixWord, tailWord_881431, baseEnd_881431] using wordTrace_append hprefix tailTrace_881431
  have hstable : (prefixWord ++ tailWord_881431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881431).length < 2 ^ (prefixWord ++ tailWord_881431).sum := by decide
  have hdescent : baseEnd_881431 < baseStart_881431 := by decide
  rcases family_descends (prefixWord ++ tailWord_881431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881464 : List Nat := [2, 1, 2, 1, 3, 2, 4, 1, 2, 3, 2]
def baseStart_881464 : Nat := 118140960795 + 881464 * 2 ^ 59
def prefixEnd_881464 : Nat := 4983230072969 + 3 ^ 40 * 881464 * 2
def baseEnd_881464 : Nat := 452614711634844501746227

theorem tailTrace_881464 : CollatzResearch.WordTrace tailWord_881464 prefixEnd_881464 452614711634844501746227 := by
  unfold tailWord_881464
  simp only [CollatzResearch.WordTrace]
  refine ⟨16074816639306972455521723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21433088852409296607362297 16074816639306972455521723)
  ·
    refine ⟨24112224958960458683282585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16074816639306972455521723 24112224958960458683282585)
    ·
      refine ⟨18084168719220344012461939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24112224958960458683282585 18084168719220344012461939)
      ·
        refine ⟨27126253078830516018692909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18084168719220344012461939 27126253078830516018692909)
        ·
          refine ⟨10172344904561443507009841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27126253078830516018692909 10172344904561443507009841)
          ·
            refine ⟨7629258678421082630257381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10172344904561443507009841 7629258678421082630257381)
            ·
              refine ⟨1430486002203952993173259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7629258678421082630257381 1430486002203952993173259)
              ·
                refine ⟨2145729003305929489759889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1430486002203952993173259 2145729003305929489759889)
                ·
                  refine ⟨1609296752479447117319917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2145729003305929489759889 1609296752479447117319917)
                  ·
                    refine ⟨603486282179792668994969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1609296752479447117319917 603486282179792668994969)
                    ·
                      refine ⟨452614711634844501746227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 603486282179792668994969 452614711634844501746227)
                      ·
                        rfl

theorem cell23_881464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 1, 2, 3, 2].length) (baseStart_881464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_881464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_881464 prefixEnd_881464 := by exact prefixLift 881464
  have htrace : WordTrace (prefixWord ++ tailWord_881464) baseStart_881464 baseEnd_881464 := by
    simpa [prefixWord, tailWord_881464, baseEnd_881464] using wordTrace_append hprefix tailTrace_881464
  have hstable : (prefixWord ++ tailWord_881464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881464).length < 2 ^ (prefixWord ++ tailWord_881464).sum := by decide
  have hdescent : baseEnd_881464 < baseStart_881464 := by decide
  rcases family_descends (prefixWord ++ tailWord_881464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881497 : List Nat := [1, 2, 1, 2, 2, 4, 1, 2, 3, 2, 3]
def baseStart_881497 : Nat := 118140960795 + 881497 * 2 ^ 59
def prefixEnd_881497 : Nat := 4983230072969 + 3 ^ 40 * 881497 * 2
def baseEnd_881497 : Nat := 452631656496442872633575

theorem tailTrace_881497 : CollatzResearch.WordTrace tailWord_881497 prefixEnd_881497 452631656496442872633575 := by
  unfold tailWord_881497
  simp only [CollatzResearch.WordTrace]
  refine ⟨32150836887494391546994745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21433891258329594364663163 32150836887494391546994745)
  ·
    refine ⟨24113127665620793660246059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32150836887494391546994745 24113127665620793660246059)
    ·
      refine ⟨36169691498431190490369089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24113127665620793660246059 36169691498431190490369089)
      ·
        refine ⟨27127268623823392867776817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36169691498431190490369089 27127268623823392867776817)
        ·
          refine ⟨20345451467867544650832613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27127268623823392867776817 20345451467867544650832613)
          ·
            refine ⟨3814772150225164622031115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20345451467867544650832613 3814772150225164622031115)
            ·
              refine ⟨5722158225337746933046673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3814772150225164622031115 5722158225337746933046673)
              ·
                refine ⟨4291618669003310199785005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5722158225337746933046673 4291618669003310199785005)
                ·
                  refine ⟨1609357000876241324919377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4291618669003310199785005 1609357000876241324919377)
                  ·
                    refine ⟨1207017750657180993689533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1609357000876241324919377 1207017750657180993689533)
                    ·
                      refine ⟨452631656496442872633575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1207017750657180993689533 452631656496442872633575)
                      ·
                        rfl

theorem cell23_881497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 3, 2, 3].length) (baseStart_881497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_881497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_881497 prefixEnd_881497 := by exact prefixLift 881497
  have htrace : WordTrace (prefixWord ++ tailWord_881497) baseStart_881497 baseEnd_881497 := by
    simpa [prefixWord, tailWord_881497, baseEnd_881497] using wordTrace_append hprefix tailTrace_881497
  have hstable : (prefixWord ++ tailWord_881497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881497).length < 2 ^ (prefixWord ++ tailWord_881497).sum := by decide
  have hdescent : baseEnd_881497 < baseStart_881497 := by decide
  rcases family_descends (prefixWord ++ tailWord_881497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881507 : List Nat := [1, 1, 1, 5, 3, 1, 1, 3, 1, 2, 4]
def baseStart_881507 : Nat := 118140960795 + 881507 * 2 ^ 59
def prefixEnd_881507 : Nat := 4983230072969 + 3 ^ 40 * 881507 * 2
def baseEnd_881507 : Nat := 452636791302987833508529

theorem tailTrace_881507 : CollatzResearch.WordTrace tailWord_881507 prefixEnd_881507 452636791302987833508529 := by
  unfold tailWord_881507
  simp only [CollatzResearch.WordTrace]
  refine ⟨32151201617458163254858775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21434134411638775503239183 32151201617458163254858775)
  ·
    refine ⟨48226802426187244882288163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32151201617458163254858775 48226802426187244882288163)
    ·
      refine ⟨72340203639280867323432245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48226802426187244882288163 72340203639280867323432245)
      ·
        refine ⟨6781894091182581311571773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72340203639280867323432245 6781894091182581311571773)
        ·
          refine ⟨2543210284193467991839415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6781894091182581311571773 2543210284193467991839415)
          ·
            refine ⟨3814815426290201987759123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2543210284193467991839415 3814815426290201987759123)
            ·
              refine ⟨5722223139435302981638685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3814815426290201987759123 5722223139435302981638685)
              ·
                refine ⟨2145833677288238618114507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5722223139435302981638685 2145833677288238618114507)
                ·
                  refine ⟨3218750515932357927171761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2145833677288238618114507 3218750515932357927171761)
                  ·
                    refine ⟨2414062886949268445378821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3218750515932357927171761 2414062886949268445378821)
                    ·
                      refine ⟨452636791302987833508529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2414062886949268445378821 452636791302987833508529)
                      ·
                        rfl

theorem cell23_881507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_881507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_881507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_881507 prefixEnd_881507 := by exact prefixLift 881507
  have htrace : WordTrace (prefixWord ++ tailWord_881507) baseStart_881507 baseEnd_881507 := by
    simpa [prefixWord, tailWord_881507, baseEnd_881507] using wordTrace_append hprefix tailTrace_881507
  have hstable : (prefixWord ++ tailWord_881507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881507).length < 2 ^ (prefixWord ++ tailWord_881507).sum := by decide
  have hdescent : baseEnd_881507 < baseStart_881507 := by decide
  rcases family_descends (prefixWord ++ tailWord_881507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881511 : List Nat := [1, 1, 5, 1, 2, 3, 1, 2, 3, 2, 2]
def baseStart_881511 : Nat := 118140960795 + 881511 * 2 ^ 59
def prefixEnd_881511 : Nat := 4983230072969 + 3 ^ 40 * 881511 * 2
def baseEnd_881511 : Nat := 452638845225605817858511

theorem tailTrace_881511 : CollatzResearch.WordTrace tailWord_881511 prefixEnd_881511 452638845225605817858511 := by
  unfold tailWord_881511
  simp only [CollatzResearch.WordTrace]
  refine ⟨32151347509443671938004387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21434231672962447958669591 32151347509443671938004387)
  ·
    refine ⟨48227021264165507907006581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32151347509443671938004387 48227021264165507907006581)
    ·
      refine ⟨4521283243515516366281867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48227021264165507907006581 4521283243515516366281867)
      ·
        refine ⟨6781924865273274549422801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4521283243515516366281867 6781924865273274549422801)
        ·
          refine ⟨5086443648954955912067101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6781924865273274549422801 5086443648954955912067101)
          ·
            refine ⟨1907416368358108467025163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5086443648954955912067101 1907416368358108467025163)
            ·
              refine ⟨2861124552537162700537745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1907416368358108467025163 2861124552537162700537745)
              ·
                refine ⟨2145843414402872025403309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2861124552537162700537745 2145843414402872025403309)
                ·
                  refine ⟨804691280401077009526241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2145843414402872025403309 804691280401077009526241)
                  ·
                    refine ⟨603518460300807757144681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 804691280401077009526241 603518460300807757144681)
                    ·
                      refine ⟨452638845225605817858511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 603518460300807757144681 452638845225605817858511)
                      ·
                        rfl

theorem cell23_881511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 2, 3, 2, 2].length) (baseStart_881511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_881511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_881511 prefixEnd_881511 := by exact prefixLift 881511
  have htrace : WordTrace (prefixWord ++ tailWord_881511) baseStart_881511 baseEnd_881511 := by
    simpa [prefixWord, tailWord_881511, baseEnd_881511] using wordTrace_append hprefix tailTrace_881511
  have hstable : (prefixWord ++ tailWord_881511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881511).length < 2 ^ (prefixWord ++ tailWord_881511).sum := by decide
  have hdescent : baseEnd_881511 < baseStart_881511 := by decide
  rcases family_descends (prefixWord ++ tailWord_881511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881534 : List Nat := [4, 2, 3, 1, 2, 1, 10]
def baseStart_881534 : Nat := 118140960795 + 881534 * 2 ^ 59
def prefixEnd_881534 : Nat := 4983230072969 + 3 ^ 40 * 881534 * 2
def baseEnd_881534 : Nat := 5588279694822953430505

theorem tailTrace_881534 : CollatzResearch.WordTrace tailWord_881534 prefixEnd_881534 5588279694822953430505 := by
  unfold tailWord_881534
  simp only [CollatzResearch.WordTrace]
  refine ⟨4019023298545043358261457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21434790925573564577394437 4019023298545043358261457)
  ·
    refine ⟨3014267473908782518696093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4019023298545043358261457 3014267473908782518696093)
    ·
      refine ⟨1130350302715793444511035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3014267473908782518696093 1130350302715793444511035)
      ·
        refine ⟨1695525454073690166766553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1130350302715793444511035 1695525454073690166766553)
        ·
          refine ⟨1271644090555267625074915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1695525454073690166766553 1271644090555267625074915)
          ·
            refine ⟨1907466135832901437612373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1271644090555267625074915 1907466135832901437612373)
            ·
              refine ⟨5588279694822953430505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1907466135832901437612373 5588279694822953430505)
              ·
                rfl

theorem cell23_881534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 10].length) (baseStart_881534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_881534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_881534 prefixEnd_881534 := by exact prefixLift 881534
  have htrace : WordTrace (prefixWord ++ tailWord_881534) baseStart_881534 baseEnd_881534 := by
    simpa [prefixWord, tailWord_881534, baseEnd_881534] using wordTrace_append hprefix tailTrace_881534
  have hstable : (prefixWord ++ tailWord_881534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881534).length < 2 ^ (prefixWord ++ tailWord_881534).sum := by decide
  have hdescent : baseEnd_881534 < baseStart_881534 := by decide
  rcases family_descends (prefixWord ++ tailWord_881534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881538 : List Nat := [3, 4, 2, 2, 1, 1, 1, 1, 4, 4]
def baseStart_881538 : Nat := 118140960795 + 881538 * 2 ^ 59
def prefixEnd_881538 : Nat := 4983230072969 + 3 ^ 40 * 881538 * 2
def baseEnd_881538 : Nat := 150884236401092404073629

theorem tailTrace_881538 : CollatzResearch.WordTrace tailWord_881538 prefixEnd_881538 150884236401092404073629 := by
  unfold tailWord_881538
  simp only [CollatzResearch.WordTrace]
  refine ⟨8038083070086463887309317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21434888186897237032824845 8038083070086463887309317)
  ·
    refine ⟨1507140575641211978870497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8038083070086463887309317 1507140575641211978870497)
    ·
      refine ⟨1130355431730908984152873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1507140575641211978870497 1130355431730908984152873)
      ·
        refine ⟨847766573798181738114655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1130355431730908984152873 847766573798181738114655)
        ·
          refine ⟨1271649860697272607171983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 847766573798181738114655 1271649860697272607171983)
          ·
            refine ⟨1907474791045908910757975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1271649860697272607171983 1907474791045908910757975)
            ·
              refine ⟨2861212186568863366136963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1907474791045908910757975 2861212186568863366136963)
              ·
                refine ⟨4291818279853295049205445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2861212186568863366136963 4291818279853295049205445)
                ·
                  refine ⟨804715927472492821726021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4291818279853295049205445 804715927472492821726021)
                  ·
                    refine ⟨150884236401092404073629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 804715927472492821726021 150884236401092404073629)
                    ·
                      rfl

theorem cell23_881538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_881538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_881538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_881538 prefixEnd_881538 := by exact prefixLift 881538
  have htrace : WordTrace (prefixWord ++ tailWord_881538) baseStart_881538 baseEnd_881538 := by
    simpa [prefixWord, tailWord_881538, baseEnd_881538] using wordTrace_append hprefix tailTrace_881538
  have hstable : (prefixWord ++ tailWord_881538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881538).length < 2 ^ (prefixWord ++ tailWord_881538).sum := by decide
  have hdescent : baseEnd_881538 < baseStart_881538 := by decide
  rcases family_descends (prefixWord ++ tailWord_881538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881558 : List Nat := [5, 3, 1, 1, 1, 1, 3, 1, 1, 2, 4]
def baseStart_881558 : Nat := 118140960795 + 881558 * 2 ^ 59
def prefixEnd_881558 : Nat := 4983230072969 + 3 ^ 40 * 881558 * 2
def baseEnd_881558 : Nat := 452662978816367133970795

theorem tailTrace_881558 : CollatzResearch.WordTrace tailWord_881558 prefixEnd_881558 452662978816367133970795 := by
  unfold tailWord_881558
  simp only [CollatzResearch.WordTrace]
  refine ⟨2009566358767087435310333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21435374493515599309976885 2009566358767087435310333)
  ·
    refine ⟨753587384537657788241375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2009566358767087435310333 753587384537657788241375)
    ·
      refine ⟨1130381076806486682362063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 753587384537657788241375 1130381076806486682362063)
      ·
        refine ⟨1695571615209730023543095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1130381076806486682362063 1695571615209730023543095)
        ·
          refine ⟨2543357422814595035314643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1695571615209730023543095 2543357422814595035314643)
          ·
            refine ⟨3815036134221892552971965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2543357422814595035314643 3815036134221892552971965)
            ·
              refine ⟨1430638550333209707364487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3815036134221892552971965 1430638550333209707364487)
              ·
                refine ⟨2145957825499814561046731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1430638550333209707364487 2145957825499814561046731)
                ·
                  refine ⟨3218936738249721841570097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2145957825499814561046731 3218936738249721841570097)
                  ·
                    refine ⟨2414202553687291381177573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3218936738249721841570097 2414202553687291381177573)
                    ·
                      refine ⟨452662978816367133970795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2414202553687291381177573 452662978816367133970795)
                      ·
                        rfl

theorem cell23_881558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_881558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_881558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_881558 prefixEnd_881558 := by exact prefixLift 881558
  have htrace : WordTrace (prefixWord ++ tailWord_881558) baseStart_881558 baseEnd_881558 := by
    simpa [prefixWord, tailWord_881558, baseEnd_881558] using wordTrace_append hprefix tailTrace_881558
  have hstable : (prefixWord ++ tailWord_881558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881558).length < 2 ^ (prefixWord ++ tailWord_881558).sum := by decide
  have hdescent : baseEnd_881558 < baseStart_881558 := by decide
  rcases family_descends (prefixWord ++ tailWord_881558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881606 : List Nat := [6, 1, 3, 1, 2, 1, 2, 1, 2, 4]
def baseStart_881606 : Nat := 118140960795 + 881606 * 2 ^ 59
def prefixEnd_881606 : Nat := 4983230072969 + 3 ^ 40 * 881606 * 2
def baseEnd_881606 : Nat := 150895875295927648723525

theorem tailTrace_881606 : CollatzResearch.WordTrace tailWord_881606 prefixEnd_881606 150895875295927648723525 := by
  unfold tailWord_881606
  simp only [CollatzResearch.WordTrace]
  refine ⟨1004837888878109473834771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21436541629399668775141781 1004837888878109473834771)
  ·
    refine ⟨1507256833317164210752157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1004837888878109473834771 1507256833317164210752157)
    ·
      refine ⟨565221312493936579032059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1507256833317164210752157 565221312493936579032059)
      ·
        refine ⟨847831968740904868548089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 565221312493936579032059 847831968740904868548089)
        ·
          refine ⟨635873976555678651411067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 847831968740904868548089 635873976555678651411067)
          ·
            refine ⟨953810964833517977116601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 635873976555678651411067 953810964833517977116601)
            ·
              refine ⟨715358223625138482837451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 953810964833517977116601 715358223625138482837451)
              ·
                refine ⟨1073037335437707724256177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 715358223625138482837451 1073037335437707724256177)
                ·
                  refine ⟨804778001578280793192133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1073037335437707724256177 804778001578280793192133)
                  ·
                    refine ⟨150895875295927648723525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 804778001578280793192133 150895875295927648723525)
                    ·
                      rfl

theorem cell23_881606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_881606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_881606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_881606 prefixEnd_881606 := by exact prefixLift 881606
  have htrace : WordTrace (prefixWord ++ tailWord_881606) baseStart_881606 baseEnd_881606 := by
    simpa [prefixWord, tailWord_881606, baseEnd_881606] using wordTrace_append hprefix tailTrace_881606
  have hstable : (prefixWord ++ tailWord_881606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881606).length < 2 ^ (prefixWord ++ tailWord_881606).sum := by decide
  have hdescent : baseEnd_881606 < baseStart_881606 := by decide
  rcases family_descends (prefixWord ++ tailWord_881606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881607 : List Nat := [1, 1, 4, 1, 1, 2, 5, 1, 7]
def baseStart_881607 : Nat := 118140960795 + 881607 * 2 ^ 59
def prefixEnd_881607 : Nat := 4983230072969 + 3 ^ 40 * 881607 * 2
def baseEnd_881607 : Nat := 50298682152048604695341

theorem tailTrace_881607 : CollatzResearch.WordTrace tailWord_881607 prefixEnd_881607 50298682152048604695341 := by
  unfold tailWord_881607
  simp only [CollatzResearch.WordTrace]
  refine ⟨32154848917095880333499075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21436565944730586888999383 32154848917095880333499075)
  ·
    refine ⟨48232273375643820500248613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32154848917095880333499075 48232273375643820500248613)
    ·
      refine ⟨9043551257933216343796615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48232273375643820500248613 9043551257933216343796615)
      ·
        refine ⟨13565326886899824515694923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9043551257933216343796615 13565326886899824515694923)
        ·
          refine ⟨20347990330349736773542385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13565326886899824515694923 20347990330349736773542385)
          ·
            refine ⟨15260992747762302580156789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20347990330349736773542385 15260992747762302580156789)
            ·
              refine ⟨1430718070102715866889699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15260992747762302580156789 1430718070102715866889699)
              ·
                refine ⟨2146077105154073800334549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1430718070102715866889699 2146077105154073800334549)
                ·
                  refine ⟨50298682152048604695341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2146077105154073800334549 50298682152048604695341)
                  ·
                    rfl

theorem cell23_881607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 1, 7].length) (baseStart_881607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_881607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_881607 prefixEnd_881607 := by exact prefixLift 881607
  have htrace : WordTrace (prefixWord ++ tailWord_881607) baseStart_881607 baseEnd_881607 := by
    simpa [prefixWord, tailWord_881607, baseEnd_881607] using wordTrace_append hprefix tailTrace_881607
  have hstable : (prefixWord ++ tailWord_881607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881607).length < 2 ^ (prefixWord ++ tailWord_881607).sum := by decide
  have hdescent : baseEnd_881607 < baseStart_881607 := by decide
  rcases family_descends (prefixWord ++ tailWord_881607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881617 : List Nat := [1, 2, 2, 1, 2, 1, 4, 1, 1, 5, 3]
def baseStart_881617 : Nat := 118140960795 + 881617 * 2 ^ 59
def prefixEnd_881617 : Nat := 4983230072969 + 3 ^ 40 * 881617 * 2
def baseEnd_881617 : Nat := 452693274174982403133023

theorem tailTrace_881617 : CollatzResearch.WordTrace tailWord_881617 prefixEnd_881617 452693274174982403133023 := by
  unfold tailWord_881617
  simp only [CollatzResearch.WordTrace]
  refine ⟨32155213647059652041363105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21436809098039768027575403 32155213647059652041363105)
  ·
    refine ⟨24116410235294739031022329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32155213647059652041363105 24116410235294739031022329)
    ·
      refine ⟨18087307676471054273266747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24116410235294739031022329 18087307676471054273266747)
      ·
        refine ⟨27130961514706581409900121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18087307676471054273266747 27130961514706581409900121)
        ·
          refine ⟨20348221136029936057425091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27130961514706581409900121 20348221136029936057425091)
          ·
            refine ⟨30522331704044904086137637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20348221136029936057425091 30522331704044904086137637)
            ·
              refine ⟨5722937194508419516150807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30522331704044904086137637 5722937194508419516150807)
              ·
                refine ⟨8584405791762629274226211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5722937194508419516150807 8584405791762629274226211)
                ·
                  refine ⟨12876608687643943911339317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8584405791762629274226211 12876608687643943911339317)
                  ·
                    refine ⟨1207182064466619741688061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12876608687643943911339317 1207182064466619741688061)
                    ·
                      refine ⟨452693274174982403133023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1207182064466619741688061 452693274174982403133023)
                      ·
                        rfl

theorem cell23_881617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 5, 3].length) (baseStart_881617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_881617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_881617 prefixEnd_881617 := by exact prefixLift 881617
  have htrace : WordTrace (prefixWord ++ tailWord_881617) baseStart_881617 baseEnd_881617 := by
    simpa [prefixWord, tailWord_881617, baseEnd_881617] using wordTrace_append hprefix tailTrace_881617
  have hstable : (prefixWord ++ tailWord_881617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881617).length < 2 ^ (prefixWord ++ tailWord_881617).sum := by decide
  have hdescent : baseEnd_881617 < baseStart_881617 := by decide
  rcases family_descends (prefixWord ++ tailWord_881617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881647 : List Nat := [1, 1, 2, 1, 4, 3, 1, 2, 1, 2, 5]
def baseStart_881647 : Nat := 118140960795 + 881647 * 2 ^ 59
def prefixEnd_881647 : Nat := 4983230072969 + 3 ^ 40 * 881647 * 2
def baseEnd_881647 : Nat := 452708678594617285757885

theorem tailTrace_881647 : CollatzResearch.WordTrace tailWord_881647 prefixEnd_881647 452708678594617285757885 := by
  unfold tailWord_881647
  simp only [CollatzResearch.WordTrace]
  refine ⟨32156307836950967164955195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21437538557967311443303463 32156307836950967164955195)
  ·
    refine ⟨48234461755426450747432793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32156307836950967164955195 48234461755426450747432793)
    ·
      refine ⟨36175846316569838060574595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48234461755426450747432793 36175846316569838060574595)
      ·
        refine ⟨54263769474854757090861893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36175846316569838060574595 54263769474854757090861893)
        ·
          refine ⟨10174456776535266954536605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54263769474854757090861893 10174456776535266954536605)
          ·
            refine ⟨3815421291200725107951227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10174456776535266954536605 3815421291200725107951227)
            ·
              refine ⟨5723131936801087661926841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3815421291200725107951227 5723131936801087661926841)
              ·
                refine ⟨4292348952600815746445131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5723131936801087661926841 4292348952600815746445131)
                ·
                  refine ⟨6438523428901223619667697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4292348952600815746445131 6438523428901223619667697)
                  ·
                    refine ⟨4828892571675917714750773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6438523428901223619667697 4828892571675917714750773)
                    ·
                      refine ⟨452708678594617285757885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4828892571675917714750773 452708678594617285757885)
                      ·
                        rfl

theorem cell23_881647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 2, 5].length) (baseStart_881647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_881647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_881647 prefixEnd_881647 := by exact prefixLift 881647
  have htrace : WordTrace (prefixWord ++ tailWord_881647) baseStart_881647 baseEnd_881647 := by
    simpa [prefixWord, tailWord_881647, baseEnd_881647] using wordTrace_append hprefix tailTrace_881647
  have hstable : (prefixWord ++ tailWord_881647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881647).length < 2 ^ (prefixWord ++ tailWord_881647).sum := by decide
  have hdescent : baseEnd_881647 < baseStart_881647 := by decide
  rcases family_descends (prefixWord ++ tailWord_881647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881718 : List Nat := [5, 1, 2, 1, 1, 3, 2, 1, 3, 4]
def baseStart_881718 : Nat := 118140960795 + 881718 * 2 ^ 59
def prefixEnd_881718 : Nat := 4983230072969 + 3 ^ 40 * 881718 * 2
def baseEnd_881718 : Nat := 150915045240362169323353

theorem tailTrace_881718 : CollatzResearch.WordTrace tailWord_881718 prefixEnd_881718 150915045240362169323353 := by
  unfold tailWord_881718
  simp only [CollatzResearch.WordTrace]
  refine ⟨2009931088730859143174363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21439264946462497527193205 2009931088730859143174363)
  ·
    refine ⟨3014896633096288714761545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2009931088730859143174363 3014896633096288714761545)
    ·
      refine ⟨2261172474822216536071159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3014896633096288714761545 2261172474822216536071159)
      ·
        refine ⟨3391758712233324804106739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2261172474822216536071159 3391758712233324804106739)
        ·
          refine ⟨5087638068349987206160109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3391758712233324804106739 5087638068349987206160109)
          ·
            refine ⟨1907864275631245202310041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5087638068349987206160109 1907864275631245202310041)
            ·
              refine ⟨1430898206723433901732531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1907864275631245202310041 1430898206723433901732531)
              ·
                refine ⟨2146347310085150852598797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1430898206723433901732531 2146347310085150852598797)
                ·
                  refine ⟨804880241281931569724549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2146347310085150852598797 804880241281931569724549)
                  ·
                    refine ⟨150915045240362169323353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 804880241281931569724549 150915045240362169323353)
                    ·
                      rfl

theorem cell23_881718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_881718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_881718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_881718 prefixEnd_881718 := by exact prefixLift 881718
  have htrace : WordTrace (prefixWord ++ tailWord_881718) baseStart_881718 baseEnd_881718 := by
    simpa [prefixWord, tailWord_881718, baseEnd_881718] using wordTrace_append hprefix tailTrace_881718
  have hstable : (prefixWord ++ tailWord_881718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881718).length < 2 ^ (prefixWord ++ tailWord_881718).sum := by decide
  have hdescent : baseEnd_881718 < baseStart_881718 := by decide
  rcases family_descends (prefixWord ++ tailWord_881718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881751 : List Nat := [1, 1, 3, 2, 2, 1, 1, 5, 2, 3, 2]
def baseStart_881751 : Nat := 118140960795 + 881751 * 2 ^ 59
def prefixEnd_881751 : Nat := 4983230072969 + 3 ^ 40 * 881751 * 2
def baseEnd_881751 : Nat := 452762080582684878857407

theorem tailTrace_881751 : CollatzResearch.WordTrace tailWord_881751 prefixEnd_881751 452762080582684878857407 := by
  unfold tailWord_881751
  simp only [CollatzResearch.WordTrace]
  refine ⟨32160101028574192926741107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21440067352382795284494071 32160101028574192926741107)
  ·
    refine ⟨48240151542861289390111661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32160101028574192926741107 48240151542861289390111661)
    ·
      refine ⟨18090056828572983521291873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48240151542861289390111661 18090056828572983521291873)
      ·
        refine ⟨13567542621429737640968905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18090056828572983521291873 13567542621429737640968905)
        ·
          refine ⟨10175656966072303230726679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13567542621429737640968905 10175656966072303230726679)
          ·
            refine ⟨15263485449108454846090019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10175656966072303230726679 15263485449108454846090019)
            ·
              refine ⟨22895228173662682269135029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15263485449108454846090019 22895228173662682269135029)
              ·
                refine ⟨2146427641280876462731409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22895228173662682269135029 2146427641280876462731409)
                ·
                  refine ⟨1609820730960657347048557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2146427641280876462731409 1609820730960657347048557)
                  ·
                    refine ⟨603682774110246505143209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1609820730960657347048557 603682774110246505143209)
                    ·
                      refine ⟨452762080582684878857407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 603682774110246505143209 452762080582684878857407)
                      ·
                        rfl

theorem cell23_881751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 5, 2, 3, 2].length) (baseStart_881751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_881751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_881751 prefixEnd_881751 := by exact prefixLift 881751
  have htrace : WordTrace (prefixWord ++ tailWord_881751) baseStart_881751 baseEnd_881751 := by
    simpa [prefixWord, tailWord_881751, baseEnd_881751] using wordTrace_append hprefix tailTrace_881751
  have hstable : (prefixWord ++ tailWord_881751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881751).length < 2 ^ (prefixWord ++ tailWord_881751).sum := by decide
  have hdescent : baseEnd_881751 < baseStart_881751 := by decide
  rcases family_descends (prefixWord ++ tailWord_881751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881764 : List Nat := [2, 3, 1, 1, 2, 1, 1, 2, 5, 1, 4]
def baseStart_881764 : Nat := 118140960795 + 881764 * 2 ^ 59
def prefixEnd_881764 : Nat := 4983230072969 + 3 ^ 40 * 881764 * 2
def baseEnd_881764 : Nat := 452768755831193327994847

theorem tailTrace_881764 : CollatzResearch.WordTrace tailWord_881764 prefixEnd_881764 452768755831193327994847 := by
  unfold tailWord_881764
  simp only [CollatzResearch.WordTrace]
  refine ⟨16080287588763548073482173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21440383451684730764642897 16080287588763548073482173)
  ·
    refine ⟨6030107845786330527555815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16080287588763548073482173 6030107845786330527555815)
    ·
      refine ⟨9045161768679495791333723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6030107845786330527555815 9045161768679495791333723)
      ·
        refine ⟨13567742653019243687000585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9045161768679495791333723 13567742653019243687000585)
        ·
          refine ⟨10175806989764432765250439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13567742653019243687000585 10175806989764432765250439)
          ·
            refine ⟨15263710484646649147875659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10175806989764432765250439 15263710484646649147875659)
            ·
              refine ⟨22895565726969973721813489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15263710484646649147875659 22895565726969973721813489)
              ·
                refine ⟨17171674295227480291360117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22895565726969973721813489 17171674295227480291360117)
                ·
                  refine ⟨1609844465177576277315011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17171674295227480291360117 1609844465177576277315011)
                  ·
                    refine ⟨2414766697766364415972517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1609844465177576277315011 2414766697766364415972517)
                    ·
                      refine ⟨452768755831193327994847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2414766697766364415972517 452768755831193327994847)
                      ·
                        rfl

theorem cell23_881764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 5, 1, 4].length) (baseStart_881764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_881764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_881764 prefixEnd_881764 := by exact prefixLift 881764
  have htrace : WordTrace (prefixWord ++ tailWord_881764) baseStart_881764 baseEnd_881764 := by
    simpa [prefixWord, tailWord_881764, baseEnd_881764] using wordTrace_append hprefix tailTrace_881764
  have hstable : (prefixWord ++ tailWord_881764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881764).length < 2 ^ (prefixWord ++ tailWord_881764).sum := by decide
  have hdescent : baseEnd_881764 < baseStart_881764 := by decide
  rcases family_descends (prefixWord ++ tailWord_881764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881775 : List Nat := [1, 1, 2, 1, 3, 3, 5, 2, 1, 1, 3]
def baseStart_881775 : Nat := 118140960795 + 881775 * 2 ^ 59
def prefixEnd_881775 : Nat := 4983230072969 + 3 ^ 40 * 881775 * 2
def baseEnd_881775 : Nat := 452774404118392784957297

theorem tailTrace_881775 : CollatzResearch.WordTrace tailWord_881775 prefixEnd_881775 452774404118392784957297 := by
  unfold tailWord_881775
  simp only [CollatzResearch.WordTrace]
  refine ⟨32160976380487245025614779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21440650920324830017076519 32160976380487245025614779)
  ·
    refine ⟨48241464570730867538422169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32160976380487245025614779 48241464570730867538422169)
    ·
      refine ⟨36181098428048150653816627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48241464570730867538422169 36181098428048150653816627)
      ·
        refine ⟨54271647642072225980724941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36181098428048150653816627 54271647642072225980724941)
        ·
          refine ⟨20351867865777084742771853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54271647642072225980724941 20351867865777084742771853)
          ·
            refine ⟨7631950449666406778539445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20351867865777084742771853 7631950449666406778539445)
            ·
              refine ⟨715495354656225635488073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7631950449666406778539445 715495354656225635488073)
              ·
                refine ⟨536621515992169226616055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 715495354656225635488073 536621515992169226616055)
                ·
                  refine ⟨804932273988253839924083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 536621515992169226616055 804932273988253839924083)
                  ·
                    refine ⟨1207398410982380759886125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 804932273988253839924083 1207398410982380759886125)
                    ·
                      refine ⟨452774404118392784957297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1207398410982380759886125 452774404118392784957297)
                      ·
                        rfl

theorem cell23_881775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5, 2, 1, 1, 3].length) (baseStart_881775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_881775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_881775 prefixEnd_881775 := by exact prefixLift 881775
  have htrace : WordTrace (prefixWord ++ tailWord_881775) baseStart_881775 baseEnd_881775 := by
    simpa [prefixWord, tailWord_881775, baseEnd_881775] using wordTrace_append hprefix tailTrace_881775
  have hstable : (prefixWord ++ tailWord_881775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881775).length < 2 ^ (prefixWord ++ tailWord_881775).sum := by decide
  have hdescent : baseEnd_881775 < baseStart_881775 := by decide
  rcases family_descends (prefixWord ++ tailWord_881775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881784 : List Nat := [2, 1, 2, 1, 1, 1, 6, 2, 1, 1, 5]
def baseStart_881784 : Nat := 118140960795 + 881784 * 2 ^ 59
def prefixEnd_881784 : Nat := 4983230072969 + 3 ^ 40 * 881784 * 2
def baseEnd_881784 : Nat := 452779025444283249744755

theorem tailTrace_881784 : CollatzResearch.WordTrace tailWord_881784 prefixEnd_881784 452779025444283249744755 := by
  unfold tailWord_881784
  simp only [CollatzResearch.WordTrace]
  refine ⟨16080652318727319781346203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21440869758303093041794937 16080652318727319781346203)
  ·
    refine ⟨24120978478090979672019305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16080652318727319781346203 24120978478090979672019305)
    ·
      refine ⟨18090733858568234754014479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24120978478090979672019305 18090733858568234754014479)
      ·
        refine ⟨27136100787852352131021719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18090733858568234754014479 27136100787852352131021719)
        ·
          refine ⟨40704151181778528196532579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27136100787852352131021719 40704151181778528196532579)
          ·
            refine ⟨61056226772667792294798869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40704151181778528196532579 61056226772667792294798869)
            ·
              refine ⟨2862010629968802763818697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 61056226772667792294798869 2862010629968802763818697)
              ·
                refine ⟨2146507972476602072864023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2862010629968802763818697 2146507972476602072864023)
                ·
                  refine ⟨3219761958714903109296035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2146507972476602072864023 3219761958714903109296035)
                  ·
                    refine ⟨4829642938072354663944053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3219761958714903109296035 4829642938072354663944053)
                    ·
                      refine ⟨452779025444283249744755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4829642938072354663944053 452779025444283249744755)
                      ·
                        rfl

theorem cell23_881784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 2, 1, 1, 5].length) (baseStart_881784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_881784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_881784 prefixEnd_881784 := by exact prefixLift 881784
  have htrace : WordTrace (prefixWord ++ tailWord_881784) baseStart_881784 baseEnd_881784 := by
    simpa [prefixWord, tailWord_881784, baseEnd_881784] using wordTrace_append hprefix tailTrace_881784
  have hstable : (prefixWord ++ tailWord_881784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881784).length < 2 ^ (prefixWord ++ tailWord_881784).sum := by decide
  have hdescent : baseEnd_881784 < baseStart_881784 := by decide
  rcases family_descends (prefixWord ++ tailWord_881784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881801 : List Nat := [1, 2, 1, 1, 4, 4, 1, 1, 3, 2, 3]
def baseStart_881801 : Nat := 118140960795 + 881801 * 2 ^ 59
def prefixEnd_881801 : Nat := 4983230072969 + 3 ^ 40 * 881801 * 2
def baseEnd_881801 : Nat := 452787754615409683232177

theorem tailTrace_881801 : CollatzResearch.WordTrace tailWord_881801 prefixEnd_881801 452787754615409683232177 := by
  unfold tailWord_881801
  simp only [CollatzResearch.WordTrace]
  refine ⟨32161924678393051466061257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21441283118928700977374171 32161924678393051466061257)
  ·
    refine ⟨24121443508794788599545943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32161924678393051466061257 24121443508794788599545943)
    ·
      refine ⟨36182165263192182899318915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24121443508794788599545943 36182165263192182899318915)
      ·
        refine ⟨54273247894788274348978373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36182165263192182899318915 54273247894788274348978373)
        ·
          refine ⟨10176233980272801440433445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54273247894788274348978373 10176233980272801440433445)
          ·
            refine ⟨1908043871301150270081271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10176233980272801440433445 1908043871301150270081271)
            ·
              refine ⟨2862065806951725405121907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1908043871301150270081271 2862065806951725405121907)
              ·
                refine ⟨4293098710427588107682861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2862065806951725405121907 4293098710427588107682861)
                ·
                  refine ⟨1609912016410345540381073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4293098710427588107682861 1609912016410345540381073)
                  ·
                    refine ⟨1207434012307759155285805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1609912016410345540381073 1207434012307759155285805)
                    ·
                      refine ⟨452787754615409683232177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1207434012307759155285805 452787754615409683232177)
                      ·
                        rfl

theorem cell23_881801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 3, 2, 3].length) (baseStart_881801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_881801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_881801 prefixEnd_881801 := by exact prefixLift 881801
  have htrace : WordTrace (prefixWord ++ tailWord_881801) baseStart_881801 baseEnd_881801 := by
    simpa [prefixWord, tailWord_881801, baseEnd_881801] using wordTrace_append hprefix tailTrace_881801
  have hstable : (prefixWord ++ tailWord_881801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881801).length < 2 ^ (prefixWord ++ tailWord_881801).sum := by decide
  have hdescent : baseEnd_881801 < baseStart_881801 := by decide
  rcases family_descends (prefixWord ++ tailWord_881801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881818 : List Nat := [3, 1, 1, 5, 1, 3, 1, 1, 1, 1, 5]
def baseStart_881818 : Nat := 118140960795 + 881818 * 2 ^ 59
def prefixEnd_881818 : Nat := 4983230072969 + 3 ^ 40 * 881818 * 2
def baseEnd_881818 : Nat := 452796483786536116719599

theorem tailTrace_881818 : CollatzResearch.WordTrace tailWord_881818 prefixEnd_881818 452796483786536116719599 := by
  unfold tailWord_881818
  simp only [CollatzResearch.WordTrace]
  refine ⟨8040636179832865842357527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21441696479554308912953405 8040636179832865842357527)
  ·
    refine ⟨12060954269749298763536291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8040636179832865842357527 12060954269749298763536291)
    ·
      refine ⟨18091431404623948145304437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12060954269749298763536291 18091431404623948145304437)
      ·
        refine ⟨1696071694183495138622291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18091431404623948145304437 1696071694183495138622291)
        ·
          refine ⟨2544107541275242707933437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1696071694183495138622291 2544107541275242707933437)
          ·
            refine ⟨954040327978216015475039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2544107541275242707933437 954040327978216015475039)
            ·
              refine ⟨1431060491967324023212559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 954040327978216015475039 1431060491967324023212559)
              ·
                refine ⟨2146590737950986034818839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1431060491967324023212559 2146590737950986034818839)
                ·
                  refine ⟨3219886106926479052228259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2146590737950986034818839 3219886106926479052228259)
                  ·
                    refine ⟨4829829160389718578342389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3219886106926479052228259 4829829160389718578342389)
                    ·
                      refine ⟨452796483786536116719599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4829829160389718578342389 452796483786536116719599)
                      ·
                        rfl

theorem cell23_881818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_881818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_881818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_881818 prefixEnd_881818 := by exact prefixLift 881818
  have htrace : WordTrace (prefixWord ++ tailWord_881818) baseStart_881818 baseEnd_881818 := by
    simpa [prefixWord, tailWord_881818, baseEnd_881818] using wordTrace_append hprefix tailTrace_881818
  have hstable : (prefixWord ++ tailWord_881818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881818).length < 2 ^ (prefixWord ++ tailWord_881818).sum := by decide
  have hdescent : baseEnd_881818 < baseStart_881818 := by decide
  rcases family_descends (prefixWord ++ tailWord_881818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881826 : List Nat := [3, 3, 1, 3, 3, 1, 2, 2, 1, 1, 3]
def baseStart_881826 : Nat := 118140960795 + 881826 * 2 ^ 59
def prefixEnd_881826 : Nat := 4983230072969 + 3 ^ 40 * 881826 * 2
def baseEnd_881826 : Nat := 452800591631772085419563

theorem tailTrace_881826 : CollatzResearch.WordTrace tailWord_881826 prefixEnd_881826 452800591631772085419563 := by
  unfold tailWord_881826
  simp only [CollatzResearch.WordTrace]
  refine ⟨8040709125825620183930333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21441891002201653823814221 8040709125825620183930333)
  ·
    refine ⟨3015265922184607568973875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8040709125825620183930333 3015265922184607568973875)
    ·
      refine ⟨4522898883276911353460813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3015265922184607568973875 4522898883276911353460813)
      ·
        refine ⟨1696087081228841757547805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4522898883276911353460813 1696087081228841757547805)
        ·
          refine ⟨636032655460815659080427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1696087081228841757547805 636032655460815659080427)
          ·
            refine ⟨954048983191223488620641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 636032655460815659080427 954048983191223488620641)
            ·
              refine ⟨715536737393417616465481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 954048983191223488620641 715536737393417616465481)
              ·
                refine ⟨536652553045063212349111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 715536737393417616465481 536652553045063212349111)
                ·
                  refine ⟨804978829567594818523667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 536652553045063212349111 804978829567594818523667)
                  ·
                    refine ⟨1207468244351392227785501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 804978829567594818523667 1207468244351392227785501)
                    ·
                      refine ⟨452800591631772085419563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1207468244351392227785501 452800591631772085419563)
                      ·
                        rfl

theorem cell23_881826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_881826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_881826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_881826 prefixEnd_881826 := by exact prefixLift 881826
  have htrace : WordTrace (prefixWord ++ tailWord_881826) baseStart_881826 baseEnd_881826 := by
    simpa [prefixWord, tailWord_881826, baseEnd_881826] using wordTrace_append hprefix tailTrace_881826
  have hstable : (prefixWord ++ tailWord_881826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881826).length < 2 ^ (prefixWord ++ tailWord_881826).sum := by decide
  have hdescent : baseEnd_881826 < baseStart_881826 := by decide
  rcases family_descends (prefixWord ++ tailWord_881826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881871 : List Nat := [1, 1, 2, 1, 1, 3, 2, 3, 3, 4, 2]
def baseStart_881871 : Nat := 118140960795 + 881871 * 2 ^ 59
def prefixEnd_881871 : Nat := 4983230072969 + 3 ^ 40 * 881871 * 2
def baseEnd_881871 : Nat := 452823698261224409356855

theorem tailTrace_881871 : CollatzResearch.WordTrace tailWord_881871 prefixEnd_881871 452823698261224409356855 := by
  unfold tailWord_881871
  simp only [CollatzResearch.WordTrace]
  refine ⟨32164477788139453421109467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21442985192092968947406311 32164477788139453421109467)
  ·
    refine ⟨48246716682209180131664201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32164477788139453421109467 48246716682209180131664201)
    ·
      refine ⟨36185037511656885098748151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48246716682209180131664201 36185037511656885098748151)
      ·
        refine ⟨54277556267485327648122227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36185037511656885098748151 54277556267485327648122227)
        ·
          refine ⟨81416334401227991472183341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54277556267485327648122227 81416334401227991472183341)
          ·
            refine ⟨30531125400460496802068753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81416334401227991472183341 30531125400460496802068753)
            ·
              refine ⟨22898344050345372601551565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30531125400460496802068753 22898344050345372601551565)
              ·
                refine ⟨8586879018879514725581837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22898344050345372601551565 8586879018879514725581837)
                ·
                  refine ⟨3220079632079818022093189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8586879018879514725581837 3220079632079818022093189)
                  ·
                    refine ⟨603764931014965879142473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3220079632079818022093189 603764931014965879142473)
                    ·
                      refine ⟨452823698261224409356855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 603764931014965879142473 452823698261224409356855)
                      ·
                        rfl

theorem cell23_881871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 3, 4, 2].length) (baseStart_881871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_881871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_881871 prefixEnd_881871 := by exact prefixLift 881871
  have htrace : WordTrace (prefixWord ++ tailWord_881871) baseStart_881871 baseEnd_881871 := by
    simpa [prefixWord, tailWord_881871, baseEnd_881871] using wordTrace_append hprefix tailTrace_881871
  have hstable : (prefixWord ++ tailWord_881871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881871).length < 2 ^ (prefixWord ++ tailWord_881871).sum := by decide
  have hdescent : baseEnd_881871 < baseStart_881871 := by decide
  rcases family_descends (prefixWord ++ tailWord_881871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881978 : List Nat := [3, 1, 1, 1, 4, 1, 4, 1, 2, 1, 4]
def baseStart_881978 : Nat := 118140960795 + 881978 * 2 ^ 59
def prefixEnd_881978 : Nat := 4983230072969 + 3 ^ 40 * 881978 * 2
def baseEnd_881978 : Nat := 452878640691255490718863

theorem tailTrace_881978 : CollatzResearch.WordTrace tailWord_881978 prefixEnd_881978 452878640691255490718863 := by
  unfold tailWord_881978
  simp only [CollatzResearch.WordTrace]
  refine ⟨8042095099687952673813647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21445586932501207130169725 8042095099687952673813647)
  ·
    refine ⟨12063142649531929010720471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8042095099687952673813647 12063142649531929010720471)
    ·
      refine ⟨18094713974297893516080707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12063142649531929010720471 18094713974297893516080707)
      ·
        refine ⟨27142070961446840274121061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18094713974297893516080707 27142070961446840274121061)
        ·
          refine ⟨5089138305271282551397699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27142070961446840274121061 5089138305271282551397699)
          ·
            refine ⟨7633707457906923827096549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5089138305271282551397699 7633707457906923827096549)
            ·
              refine ⟨1431320148357548217580603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7633707457906923827096549 1431320148357548217580603)
              ·
                refine ⟨2146980222536322326370905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1431320148357548217580603 2146980222536322326370905)
                ·
                  refine ⟨1610235166902241744778179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2146980222536322326370905 1610235166902241744778179)
                  ·
                    refine ⟨2415352750353362617167269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1610235166902241744778179 2415352750353362617167269)
                    ·
                      refine ⟨452878640691255490718863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2415352750353362617167269 452878640691255490718863)
                      ·
                        rfl

theorem cell23_881978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 1, 2, 1, 4].length) (baseStart_881978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_881978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_881978 prefixEnd_881978 := by exact prefixLift 881978
  have htrace : WordTrace (prefixWord ++ tailWord_881978) baseStart_881978 baseEnd_881978 := by
    simpa [prefixWord, tailWord_881978, baseEnd_881978] using wordTrace_append hprefix tailTrace_881978
  have hstable : (prefixWord ++ tailWord_881978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881978).length < 2 ^ (prefixWord ++ tailWord_881978).sum := by decide
  have hdescent : baseEnd_881978 < baseStart_881978 := by decide
  rcases family_descends (prefixWord ++ tailWord_881978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881998 : List Nat := [4, 1, 1, 1, 1, 1, 3, 4, 2, 2, 3]
def baseStart_881998 : Nat := 118140960795 + 881998 * 2 ^ 59
def prefixEnd_881998 : Nat := 4983230072969 + 3 ^ 40 * 881998 * 2
def baseEnd_881998 : Nat := 452888910304345412468771

theorem tailTrace_881998 : CollatzResearch.WordTrace tailWord_881998 prefixEnd_881998 452888910304345412468771 := by
  unfold tailWord_881998
  simp only [CollatzResearch.WordTrace]
  refine ⟨4021138732334919263872831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21446073239119569407321765 4021138732334919263872831)
  ·
    refine ⟨6031708098502378895809247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4021138732334919263872831 6031708098502378895809247)
    ·
      refine ⟨9047562147753568343713871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6031708098502378895809247 9047562147753568343713871)
      ·
        refine ⟨13571343221630352515570807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9047562147753568343713871 13571343221630352515570807)
        ·
          refine ⟨20357014832445528773356211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13571343221630352515570807 20357014832445528773356211)
          ·
            refine ⟨30535522248668293160034317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20357014832445528773356211 30535522248668293160034317)
            ·
              refine ⟨11450820843250609935012869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30535522248668293160034317 11450820843250609935012869)
              ·
                refine ⟨2147028908109489362814913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11450820843250609935012869 2147028908109489362814913)
                ·
                  refine ⟨1610271681082117022111185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2147028908109489362814913 1610271681082117022111185)
                  ·
                    refine ⟨1207703760811587766583389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1610271681082117022111185 1207703760811587766583389)
                    ·
                      refine ⟨452888910304345412468771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1207703760811587766583389 452888910304345412468771)
                      ·
                        rfl

theorem cell23_881998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 4, 2, 2, 3].length) (baseStart_881998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_881998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_881998 prefixEnd_881998 := by exact prefixLift 881998
  have htrace : WordTrace (prefixWord ++ tailWord_881998) baseStart_881998 baseEnd_881998 := by
    simpa [prefixWord, tailWord_881998, baseEnd_881998] using wordTrace_append hprefix tailTrace_881998
  have hstable : (prefixWord ++ tailWord_881998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881998).length < 2 ^ (prefixWord ++ tailWord_881998).sum := by decide
  have hdescent : baseEnd_881998 < baseStart_881998 := by decide
  rcases family_descends (prefixWord ++ tailWord_881998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882018 : List Nat := [3, 3, 2, 1, 1, 1, 1, 5, 6]
def baseStart_882018 : Nat := 118140960795 + 882018 * 2 ^ 59
def prefixEnd_882018 : Nat := 4983230072969 + 3 ^ 40 * 882018 * 2
def baseEnd_882018 : Nat := 50322131101937259357631

theorem tailTrace_882018 : CollatzResearch.WordTrace tailWord_882018 prefixEnd_882018 50322131101937259357631 := by
  unfold tailWord_882018
  simp only [CollatzResearch.WordTrace]
  refine ⟨8042459829651724381677677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21446559545737931684473805 8042459829651724381677677)
  ·
    refine ⟨3015922436119396643129129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8042459829651724381677677 3015922436119396643129129)
    ·
      refine ⟨2261941827089547482346847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3015922436119396643129129 2261941827089547482346847)
      ·
        refine ⟨3392912740634321223520271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2261941827089547482346847 3392912740634321223520271)
        ·
          refine ⟨5089369110951481835280407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3392912740634321223520271 5089369110951481835280407)
          ·
            refine ⟨7634053666427222752920611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5089369110951481835280407 7634053666427222752920611)
            ·
              refine ⟨11451080499640834129380917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7634053666427222752920611 11451080499640834129380917)
              ·
                refine ⟨1073538796841328199629461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11451080499640834129380917 1073538796841328199629461)
                ·
                  refine ⟨50322131101937259357631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1073538796841328199629461 50322131101937259357631)
                  ·
                    rfl

theorem cell23_882018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 5, 6].length) (baseStart_882018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_882018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_882018 prefixEnd_882018 := by exact prefixLift 882018
  have htrace : WordTrace (prefixWord ++ tailWord_882018) baseStart_882018 baseEnd_882018 := by
    simpa [prefixWord, tailWord_882018, baseEnd_882018] using wordTrace_append hprefix tailTrace_882018
  have hstable : (prefixWord ++ tailWord_882018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882018).length < 2 ^ (prefixWord ++ tailWord_882018).sum := by decide
  have hdescent : baseEnd_882018 < baseStart_882018 := by decide
  rcases family_descends (prefixWord ++ tailWord_882018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882031 : List Nat := [1, 1, 2, 1, 3, 1, 3, 3, 3, 5]
def baseStart_882031 : Nat := 118140960795 + 882031 * 2 ^ 59
def prefixEnd_882031 : Nat := 4983230072969 + 3 ^ 40 * 882031 * 2
def baseEnd_882031 : Nat := 150968618388647927785373

theorem tailTrace_882031 : CollatzResearch.WordTrace tailWord_882031 prefixEnd_882031 150968618388647927785373 := by
  unfold tailWord_882031
  simp only [CollatzResearch.WordTrace]
  refine ⟨32170313467559800746933947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21446875645039867164622631 32170313467559800746933947)
  ·
    refine ⟨48255470201339701120400921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32170313467559800746933947 48255470201339701120400921)
    ·
      refine ⟨36191602651004775840300691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48255470201339701120400921 36191602651004775840300691)
      ·
        refine ⟨54287403976507163760451037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36191602651004775840300691 54287403976507163760451037)
        ·
          refine ⟨20357776491190186410169139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54287403976507163760451037 20357776491190186410169139)
          ·
            refine ⟨30536664736785279615253709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20357776491190186410169139 30536664736785279615253709)
            ·
              refine ⟨11451249276294479855720141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30536664736785279615253709 11451249276294479855720141)
              ·
                refine ⟨4294218478610429945895053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11451249276294479855720141 4294218478610429945895053)
                ·
                  refine ⟨1610331929478911229710645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4294218478610429945895053 1610331929478911229710645)
                  ·
                    refine ⟨150968618388647927785373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1610331929478911229710645 150968618388647927785373)
                    ·
                      rfl

theorem cell23_882031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 3, 5].length) (baseStart_882031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_882031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_882031 prefixEnd_882031 := by exact prefixLift 882031
  have htrace : WordTrace (prefixWord ++ tailWord_882031) baseStart_882031 baseEnd_882031 := by
    simpa [prefixWord, tailWord_882031, baseEnd_882031] using wordTrace_append hprefix tailTrace_882031
  have hstable : (prefixWord ++ tailWord_882031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882031).length < 2 ^ (prefixWord ++ tailWord_882031).sum := by decide
  have hdescent : baseEnd_882031 < baseStart_882031 := by decide
  rcases family_descends (prefixWord ++ tailWord_882031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882085 : List Nat := [1, 3, 1, 2, 1, 1, 2, 3, 5, 2, 2]
def baseStart_882085 : Nat := 118140960795 + 882085 * 2 ^ 59
def prefixEnd_882085 : Nat := 4983230072969 + 3 ^ 40 * 882085 * 2
def baseEnd_882085 : Nat := 452933583121286572080871

theorem tailTrace_882085 : CollatzResearch.WordTrace tailWord_882085 prefixEnd_882085 452933583121286572080871 := by
  unfold tailWord_882085
  simp only [CollatzResearch.WordTrace]
  refine ⟨32172283009364167969399709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21448188672909445312933139 32172283009364167969399709)
  ·
    refine ⟨12064606128511562988524891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32172283009364167969399709 12064606128511562988524891)
    ·
      refine ⟨18096909192767344482787337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12064606128511562988524891 18096909192767344482787337)
      ·
        refine ⟨13572681894575508362090503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18096909192767344482787337 13572681894575508362090503)
        ·
          refine ⟨20359022841863262543135755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13572681894575508362090503 20359022841863262543135755)
          ·
            refine ⟨30538534262794893814703633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20359022841863262543135755 30538534262794893814703633)
            ·
              refine ⟨22903900697096170361027725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30538534262794893814703633 22903900697096170361027725)
              ·
                refine ⟨8588962761411063885385397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22903900697096170361027725 8588962761411063885385397)
                ·
                  refine ⟨805215258882287239254881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8588962761411063885385397 805215258882287239254881)
                  ·
                    refine ⟨603911444161715429441161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 805215258882287239254881 603911444161715429441161)
                    ·
                      refine ⟨452933583121286572080871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 603911444161715429441161 452933583121286572080871)
                      ·
                        rfl

theorem cell23_882085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 5, 2, 2].length) (baseStart_882085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_882085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_882085 prefixEnd_882085 := by exact prefixLift 882085
  have htrace : WordTrace (prefixWord ++ tailWord_882085) baseStart_882085 baseEnd_882085 := by
    simpa [prefixWord, tailWord_882085, baseEnd_882085] using wordTrace_append hprefix tailTrace_882085
  have hstable : (prefixWord ++ tailWord_882085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882085).length < 2 ^ (prefixWord ++ tailWord_882085).sum := by decide
  have hdescent : baseEnd_882085 < baseStart_882085 := by decide
  rcases family_descends (prefixWord ++ tailWord_882085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882105 : List Nat := [1, 2, 1, 4, 4, 1, 2, 1, 1, 1, 5]
def baseStart_882105 : Nat := 118140960795 + 882105 * 2 ^ 59
def prefixEnd_882105 : Nat := 4983230072969 + 3 ^ 40 * 882105 * 2
def baseEnd_882105 : Nat := 452943852734376493830779

theorem tailTrace_882105 : CollatzResearch.WordTrace tailWord_882105 prefixEnd_882105 452943852734376493830779 := by
  unfold tailWord_882105
  simp only [CollatzResearch.WordTrace]
  refine ⟨32173012469291711385127769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21448674979527807590085179 32173012469291711385127769)
  ·
    refine ⟨24129759351968783538845827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32173012469291711385127769 24129759351968783538845827)
    ·
      refine ⟨36194639027953175308268741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24129759351968783538845827 36194639027953175308268741)
      ·
        refine ⟨6786494817741220370300389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36194639027953175308268741 6786494817741220370300389)
        ·
          refine ⟨1272467778326478819431323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6786494817741220370300389 1272467778326478819431323)
          ·
            refine ⟨1908701667489718229146985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1272467778326478819431323 1908701667489718229146985)
            ·
              refine ⟨1431526250617288671860239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1908701667489718229146985 1431526250617288671860239)
              ·
                refine ⟨2147289375925933007790359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1431526250617288671860239 2147289375925933007790359)
                ·
                  refine ⟨3220934063888899511685539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2147289375925933007790359 3220934063888899511685539)
                  ·
                    refine ⟨4831401095833349267528309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3220934063888899511685539 4831401095833349267528309)
                    ·
                      refine ⟨452943852734376493830779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4831401095833349267528309 452943852734376493830779)
                      ·
                        rfl

theorem cell23_882105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_882105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_882105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_882105 prefixEnd_882105 := by exact prefixLift 882105
  have htrace : WordTrace (prefixWord ++ tailWord_882105) baseStart_882105 baseEnd_882105 := by
    simpa [prefixWord, tailWord_882105, baseEnd_882105] using wordTrace_append hprefix tailTrace_882105
  have hstable : (prefixWord ++ tailWord_882105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882105).length < 2 ^ (prefixWord ++ tailWord_882105).sum := by decide
  have hdescent : baseEnd_882105 < baseStart_882105 := by decide
  rcases family_descends (prefixWord ++ tailWord_882105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882121 : List Nat := [1, 2, 1, 1, 2, 1, 3, 3, 2, 7]
def baseStart_882121 : Nat := 118140960795 + 882121 * 2 ^ 59
def prefixEnd_882121 : Nat := 4983230072969 + 3 ^ 40 * 882121 * 2
def baseEnd_882121 : Nat := 150984022808282810410235

theorem tailTrace_882121 : CollatzResearch.WordTrace tailWord_882121 prefixEnd_882121 150984022808282810410235 := by
  unfold tailWord_882121
  simp only [CollatzResearch.WordTrace]
  refine ⟨32173596037233746117710217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21449064024822497411806811 32173596037233746117710217)
  ·
    refine ⟨24130197027925309588282663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32173596037233746117710217 24130197027925309588282663)
    ·
      refine ⟨36195295541887964382423995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24130197027925309588282663 36195295541887964382423995)
      ·
        refine ⟨54292943312831946573635993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36195295541887964382423995 54292943312831946573635993)
        ·
          refine ⟨40719707484623959930226995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54292943312831946573635993 40719707484623959930226995)
          ·
            refine ⟨61079561226935939895340493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40719707484623959930226995 61079561226935939895340493)
            ·
              refine ⟨22904835460100977460752685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61079561226935939895340493 22904835460100977460752685)
              ·
                refine ⟨8589313297537866547782257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22904835460100977460752685 8589313297537866547782257)
                ·
                  refine ⟨6441984973153399910836693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8589313297537866547782257 6441984973153399910836693)
                  ·
                    refine ⟨150984022808282810410235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6441984973153399910836693 150984022808282810410235)
                    ·
                      rfl

theorem cell23_882121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 7].length) (baseStart_882121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_882121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_882121 prefixEnd_882121 := by exact prefixLift 882121
  have htrace : WordTrace (prefixWord ++ tailWord_882121) baseStart_882121 baseEnd_882121 := by
    simpa [prefixWord, tailWord_882121, baseEnd_882121] using wordTrace_append hprefix tailTrace_882121
  have hstable : (prefixWord ++ tailWord_882121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882121).length < 2 ^ (prefixWord ++ tailWord_882121).sum := by decide
  have hdescent : baseEnd_882121 < baseStart_882121 := by decide
  rcases family_descends (prefixWord ++ tailWord_882121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882265 : List Nat := [1, 2, 1, 2, 2, 1, 1, 4, 1, 6, 2]
def baseStart_882265 : Nat := 118140960795 + 882265 * 2 ^ 59
def prefixEnd_882265 : Nat := 4983230072969 + 3 ^ 40 * 882265 * 2
def baseEnd_882265 : Nat := 453026009639095867830043

theorem tailTrace_882265 : CollatzResearch.WordTrace tailWord_882265 prefixEnd_882265 453026009639095867830043 := by
  unfold tailWord_882265
  simp only [CollatzResearch.WordTrace]
  refine ⟨32178848148712058710952249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21452565432474705807301499 32178848148712058710952249)
  ·
    refine ⟨24134136111534044033214187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32178848148712058710952249 24134136111534044033214187)
    ·
      refine ⟨36201204167301066049821281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24134136111534044033214187 36201204167301066049821281)
      ·
        refine ⟨27150903125475799537365961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36201204167301066049821281 27150903125475799537365961)
        ·
          refine ⟨20363177344106849653024471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27150903125475799537365961 20363177344106849653024471)
          ·
            refine ⟨30544766016160274479536707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20363177344106849653024471 30544766016160274479536707)
            ·
              refine ⟨45817149024240411719305061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30544766016160274479536707 45817149024240411719305061)
              ·
                refine ⟨8590715442045077197369699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45817149024240411719305061 8590715442045077197369699)
                ·
                  refine ⟨12886073163067615796054549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8590715442045077197369699 12886073163067615796054549)
                  ·
                    refine ⟨604034679518794490440057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12886073163067615796054549 604034679518794490440057)
                    ·
                      refine ⟨453026009639095867830043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 604034679518794490440057 453026009639095867830043)
                      ·
                        rfl

theorem cell23_882265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 6, 2].length) (baseStart_882265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_882265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_882265 prefixEnd_882265 := by exact prefixLift 882265
  have htrace : WordTrace (prefixWord ++ tailWord_882265) baseStart_882265 baseEnd_882265 := by
    simpa [prefixWord, tailWord_882265, baseEnd_882265] using wordTrace_append hprefix tailTrace_882265
  have hstable : (prefixWord ++ tailWord_882265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882265).length < 2 ^ (prefixWord ++ tailWord_882265).sum := by decide
  have hdescent : baseEnd_882265 < baseStart_882265 := by decide
  rcases family_descends (prefixWord ++ tailWord_882265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882282 : List Nat := [3, 1, 3, 2, 1, 3, 1, 2, 2, 1, 4]
def baseStart_882282 : Nat := 118140960795 + 882282 * 2 ^ 59
def prefixEnd_882282 : Nat := 4983230072969 + 3 ^ 40 * 882282 * 2
def baseEnd_882282 : Nat := 453034738810222301317465

theorem tailTrace_882282 : CollatzResearch.WordTrace tailWord_882282 prefixEnd_882282 453034738810222301317465 := by
  unfold tailWord_882282
  simp only [CollatzResearch.WordTrace]
  refine ⟨8044867047412617653580275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21452978793100313742880733 8044867047412617653580275)
  ·
    refine ⟨12067300571118926480370413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8044867047412617653580275 12067300571118926480370413)
    ·
      refine ⟨4525237714169597430138905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12067300571118926480370413 4525237714169597430138905)
      ·
        refine ⟨3393928285627198072604179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4525237714169597430138905 3393928285627198072604179)
        ·
          refine ⟨5090892428440797108906269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3393928285627198072604179 5090892428440797108906269)
          ·
            refine ⟨1909084660665298915839851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5090892428440797108906269 1909084660665298915839851)
            ·
              refine ⟨2863626990997948373759777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1909084660665298915839851 2863626990997948373759777)
              ·
                refine ⟨2147720243248461280319833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2863626990997948373759777 2147720243248461280319833)
                ·
                  refine ⟨1610790182436345960239875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2147720243248461280319833 1610790182436345960239875)
                  ·
                    refine ⟨2416185273654518940359813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1610790182436345960239875 2416185273654518940359813)
                    ·
                      refine ⟨453034738810222301317465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2416185273654518940359813 453034738810222301317465)
                      ·
                        rfl

theorem cell23_882282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_882282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_882282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_882282 prefixEnd_882282 := by exact prefixLift 882282
  have htrace : WordTrace (prefixWord ++ tailWord_882282) baseStart_882282 baseEnd_882282 := by
    simpa [prefixWord, tailWord_882282, baseEnd_882282] using wordTrace_append hprefix tailTrace_882282
  have hstable : (prefixWord ++ tailWord_882282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882282).length < 2 ^ (prefixWord ++ tailWord_882282).sum := by decide
  have hdescent : baseEnd_882282 < baseStart_882282 := by decide
  rcases family_descends (prefixWord ++ tailWord_882282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882349 : List Nat := [1, 5, 2, 1, 1, 1, 2, 3, 3, 1, 3]
def baseStart_882349 : Nat := 118140960795 + 882349 * 2 ^ 59
def prefixEnd_882349 : Nat := 4983230072969 + 3 ^ 40 * 882349 * 2
def baseEnd_882349 : Nat := 453069142014073539179657

theorem tailTrace_882349 : CollatzResearch.WordTrace tailWord_882349 prefixEnd_882349 453069142014073539179657 := by
  unfold tailWord_882349
  simp only [CollatzResearch.WordTrace]
  refine ⟨32181911880407741057010101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21454607920271827371340067 32181911880407741057010101)
  ·
    refine ⟨3017054238788225724094697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32181911880407741057010101 3017054238788225724094697)
    ·
      refine ⟨2262790679091169293071023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3017054238788225724094697 2262790679091169293071023)
      ·
        refine ⟨3394186018636753939606535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2262790679091169293071023 3394186018636753939606535)
        ·
          refine ⟨5091279027955130909409803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3394186018636753939606535 5091279027955130909409803)
          ·
            refine ⟨7636918541932696364114705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5091279027955130909409803 7636918541932696364114705)
            ·
              refine ⟨5727688906449522273086029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7636918541932696364114705 5727688906449522273086029)
              ·
                refine ⟨2147883339918570852407261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5727688906449522273086029 2147883339918570852407261)
                ·
                  refine ⟨805456252469464069652723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2147883339918570852407261 805456252469464069652723)
                  ·
                    refine ⟨1208184378704196104479085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 805456252469464069652723 1208184378704196104479085)
                    ·
                      refine ⟨453069142014073539179657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1208184378704196104479085 453069142014073539179657)
                      ·
                        rfl

theorem cell23_882349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_882349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_882349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_882349 prefixEnd_882349 := by exact prefixLift 882349
  have htrace : WordTrace (prefixWord ++ tailWord_882349) baseStart_882349 baseEnd_882349 := by
    simpa [prefixWord, tailWord_882349, baseEnd_882349] using wordTrace_append hprefix tailTrace_882349
  have hstable : (prefixWord ++ tailWord_882349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882349).length < 2 ^ (prefixWord ++ tailWord_882349).sum := by decide
  have hdescent : baseEnd_882349 < baseStart_882349 := by decide
  rcases family_descends (prefixWord ++ tailWord_882349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882355 : List Nat := [1, 1, 1, 2, 3, 3, 1, 1, 5, 1, 4]
def baseStart_882355 : Nat := 118140960795 + 882355 * 2 ^ 59
def prefixEnd_882355 : Nat := 4983230072969 + 3 ^ 40 * 882355 * 2
def baseEnd_882355 : Nat := 453072222898000515704629

theorem tailTrace_882355 : CollatzResearch.WordTrace tailWord_882355 prefixEnd_882355 453072222898000515704629 := by
  unfold tailWord_882355
  simp only [CollatzResearch.WordTrace]
  refine ⟨32182130718386004081728519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21454753812257336054485679 32182130718386004081728519)
  ·
    refine ⟨48273196077579006122592779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32182130718386004081728519 48273196077579006122592779)
    ·
      refine ⟨72409794116368509183889169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48273196077579006122592779 72409794116368509183889169)
      ·
        refine ⟨54307345587276381887916877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72409794116368509183889169 54307345587276381887916877)
        ·
          refine ⟨20365254595228643207968829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54307345587276381887916877 20365254595228643207968829)
          ·
            refine ⟨7636970473210741202988311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20365254595228643207968829 7636970473210741202988311)
            ·
              refine ⟨11455455709816111804482467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7636970473210741202988311 11455455709816111804482467)
              ·
                refine ⟨17183183564724167706723701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11455455709816111804482467 17183183564724167706723701)
                ·
                  refine ⟨1610923459192890722505347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17183183564724167706723701 1610923459192890722505347)
                  ·
                    refine ⟨2416385188789336083758021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1610923459192890722505347 2416385188789336083758021)
                    ·
                      refine ⟨453072222898000515704629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2416385188789336083758021 453072222898000515704629)
                      ·
                        rfl

theorem cell23_882355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 5, 1, 4].length) (baseStart_882355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_882355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_882355 prefixEnd_882355 := by exact prefixLift 882355
  have htrace : WordTrace (prefixWord ++ tailWord_882355) baseStart_882355 baseEnd_882355 := by
    simpa [prefixWord, tailWord_882355, baseEnd_882355] using wordTrace_append hprefix tailTrace_882355
  have hstable : (prefixWord ++ tailWord_882355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882355).length < 2 ^ (prefixWord ++ tailWord_882355).sum := by decide
  have hdescent : baseEnd_882355 < baseStart_882355 := by decide
  rcases family_descends (prefixWord ++ tailWord_882355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882370 : List Nat := [3, 5, 1, 2, 1, 2, 1, 1, 2, 2, 3]
def baseStart_882370 : Nat := 118140960795 + 882370 * 2 ^ 59
def prefixEnd_882370 : Nat := 4983230072969 + 3 ^ 40 * 882370 * 2
def baseEnd_882370 : Nat := 453079925107817957017061

theorem tailTrace_882370 : CollatzResearch.WordTrace tailWord_882370 prefixEnd_882370 453079925107817957017061 := by
  unfold tailWord_882370
  simp only [CollatzResearch.WordTrace]
  refine ⟨8045669453332915410881141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21455118542221107762349709 8045669453332915410881141)
  ·
    refine ⟨754281511249960819770107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8045669453332915410881141 754281511249960819770107)
    ·
      refine ⟨1131422266874941229655161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 754281511249960819770107 1131422266874941229655161)
      ·
        refine ⟨848566700156205922241371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1131422266874941229655161 848566700156205922241371)
        ·
          refine ⟨1272850050234308883362057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 848566700156205922241371 1272850050234308883362057)
          ·
            refine ⟨954637537675731662521543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1272850050234308883362057 954637537675731662521543)
            ·
              refine ⟨1431956306513597493782315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 954637537675731662521543 1431956306513597493782315)
              ·
                refine ⟨2147934459770396240673473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1431956306513597493782315 2147934459770396240673473)
                ·
                  refine ⟨1610950844827797180505105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2147934459770396240673473 1610950844827797180505105)
                  ·
                    refine ⟨1208213133620847885378829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1610950844827797180505105 1208213133620847885378829)
                    ·
                      refine ⟨453079925107817957017061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1208213133620847885378829 453079925107817957017061)
                      ·
                        rfl

theorem cell23_882370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_882370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_882370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_882370 prefixEnd_882370 := by exact prefixLift 882370
  have htrace : WordTrace (prefixWord ++ tailWord_882370) baseStart_882370 baseEnd_882370 := by
    simpa [prefixWord, tailWord_882370, baseEnd_882370] using wordTrace_append hprefix tailTrace_882370
  have hstable : (prefixWord ++ tailWord_882370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882370).length < 2 ^ (prefixWord ++ tailWord_882370).sum := by decide
  have hdescent : baseEnd_882370 < baseStart_882370 := by decide
  rcases family_descends (prefixWord ++ tailWord_882370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882372 : List Nat := [2, 3, 3, 1, 1, 1, 1, 3, 3, 1, 4]
def baseStart_882372 : Nat := 118140960795 + 882372 * 2 ^ 59
def prefixEnd_882372 : Nat := 4983230072969 + 3 ^ 40 * 882372 * 2
def baseEnd_882372 : Nat := 453080952069126949192051

theorem tailTrace_882372 : CollatzResearch.WordTrace tailWord_882372 prefixEnd_882372 453080952069126949192051 := by
  unfold tailWord_882372
  simp only [CollatzResearch.WordTrace]
  refine ⟨16091375379662207992548685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21455167172882943990064913 16091375379662207992548685)
  ·
    refine ⟨6034265767373327997205757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16091375379662207992548685 6034265767373327997205757)
    ·
      refine ⟨2262849662764997998952159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6034265767373327997205757 2262849662764997998952159)
      ·
        refine ⟨3394274494147496998428239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2262849662764997998952159 3394274494147496998428239)
        ·
          refine ⟨5091411741221245497642359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3394274494147496998428239 5091411741221245497642359)
          ·
            refine ⟨7637117611831868246463539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5091411741221245497642359 7637117611831868246463539)
            ·
              refine ⟨11455676417747802369695309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7637117611831868246463539 11455676417747802369695309)
              ·
                refine ⟨4295878656655425888635741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11455676417747802369695309 4295878656655425888635741)
                ·
                  refine ⟨1610954496245784708238403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4295878656655425888635741 1610954496245784708238403)
                  ·
                    refine ⟨2416431744368677062357605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1610954496245784708238403 2416431744368677062357605)
                    ·
                      refine ⟨453080952069126949192051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2416431744368677062357605 453080952069126949192051)
                      ·
                        rfl

theorem cell23_882372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_882372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_882372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_882372 prefixEnd_882372 := by exact prefixLift 882372
  have htrace : WordTrace (prefixWord ++ tailWord_882372) baseStart_882372 baseEnd_882372 := by
    simpa [prefixWord, tailWord_882372, baseEnd_882372] using wordTrace_append hprefix tailTrace_882372
  have hstable : (prefixWord ++ tailWord_882372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882372).length < 2 ^ (prefixWord ++ tailWord_882372).sum := by decide
  have hdescent : baseEnd_882372 < baseStart_882372 := by decide
  rcases family_descends (prefixWord ++ tailWord_882372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882382 : List Nat := [4, 1, 1, 1, 3, 1, 2, 2, 4, 4]
def baseStart_882382 : Nat := 118140960795 + 882382 * 2 ^ 59
def prefixEnd_882382 : Nat := 4983230072969 + 3 ^ 40 * 882382 * 2
def baseEnd_882382 : Nat := 151028695625223970022335

theorem tailTrace_882382 : CollatzResearch.WordTrace tailWord_882382 prefixEnd_882382 151028695625223970022335 := by
  unfold tailWord_882382
  simp only [CollatzResearch.WordTrace]
  refine ⟨4022889436161023461620175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21455410326192125128640933 4022889436161023461620175)
  ·
    refine ⟨6034334154241535192430263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4022889436161023461620175 6034334154241535192430263)
    ·
      refine ⟨9051501231362302788645395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6034334154241535192430263 9051501231362302788645395)
      ·
        refine ⟨13577251847043454182968093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9051501231362302788645395 13577251847043454182968093)
        ·
          refine ⟨5091469442641295318613035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13577251847043454182968093 5091469442641295318613035)
          ·
            refine ⟨7637204163961942977919553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5091469442641295318613035 7637204163961942977919553)
            ·
              refine ⟨5727903122971457233439665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7637204163961942977919553 5727903122971457233439665)
              ·
                refine ⟨4295927342228592925079749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5727903122971457233439665 4295927342228592925079749)
                ·
                  refine ⟨805486376667861173452453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4295927342228592925079749 805486376667861173452453)
                  ·
                    refine ⟨151028695625223970022335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 805486376667861173452453 151028695625223970022335)
                    ·
                      rfl

theorem cell23_882382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 4, 4].length) (baseStart_882382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_882382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_882382 prefixEnd_882382 := by exact prefixLift 882382
  have htrace : WordTrace (prefixWord ++ tailWord_882382) baseStart_882382 baseEnd_882382 := by
    simpa [prefixWord, tailWord_882382, baseEnd_882382] using wordTrace_append hprefix tailTrace_882382
  have hstable : (prefixWord ++ tailWord_882382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882382).length < 2 ^ (prefixWord ++ tailWord_882382).sum := by decide
  have hdescent : baseEnd_882382 < baseStart_882382 := by decide
  rcases family_descends (prefixWord ++ tailWord_882382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882386 : List Nat := [3, 2, 2, 2, 2, 3, 2, 1, 1, 5]
def baseStart_882386 : Nat := 118140960795 + 882386 * 2 ^ 59
def prefixEnd_882386 : Nat := 4983230072969 + 3 ^ 40 * 882386 * 2
def baseEnd_882386 : Nat := 151029380266096631472329

theorem tailTrace_882386 : CollatzResearch.WordTrace tailWord_882386 prefixEnd_882386 151029380266096631472329 := by
  unfold tailWord_882386
  simp only [CollatzResearch.WordTrace]
  refine ⟨8045815345318424094026753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21455507587515797584071341 8045815345318424094026753)
  ·
    refine ⟨6034361508988818070520065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8045815345318424094026753 6034361508988818070520065)
    ·
      refine ⟨4525771131741613552890049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6034361508988818070520065 4525771131741613552890049)
      ·
        refine ⟨3394328348806210164667537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4525771131741613552890049 3394328348806210164667537)
        ·
          refine ⟨2545746261604657623500653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3394328348806210164667537 2545746261604657623500653)
          ·
            refine ⟨954654848101746608812745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2545746261604657623500653 954654848101746608812745)
            ·
              refine ⟨715991136076309956609559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 954654848101746608812745 715991136076309956609559)
              ·
                refine ⟨1073986704114464934914339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 715991136076309956609559 1073986704114464934914339)
                ·
                  refine ⟨1610980056171697402371509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1073986704114464934914339 1610980056171697402371509)
                  ·
                    refine ⟨151029380266096631472329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1610980056171697402371509 151029380266096631472329)
                    ·
                      rfl

theorem cell23_882386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 2, 1, 1, 5].length) (baseStart_882386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_882386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_882386 prefixEnd_882386 := by exact prefixLift 882386
  have htrace : WordTrace (prefixWord ++ tailWord_882386) baseStart_882386 baseEnd_882386 := by
    simpa [prefixWord, tailWord_882386, baseEnd_882386] using wordTrace_append hprefix tailTrace_882386
  have hstable : (prefixWord ++ tailWord_882386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882386).length < 2 ^ (prefixWord ++ tailWord_882386).sum := by decide
  have hdescent : baseEnd_882386 < baseStart_882386 := by decide
  rcases family_descends (prefixWord ++ tailWord_882386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882435 : List Nat := [1, 1, 1, 3, 2, 2, 3, 1, 2, 2, 5]
def baseStart_882435 : Nat := 118140960795 + 882435 * 2 ^ 59
def prefixEnd_882435 : Nat := 4983230072969 + 3 ^ 40 * 882435 * 2
def baseEnd_882435 : Nat := 453113301350360202704261

theorem tailTrace_882435 : CollatzResearch.WordTrace tailWord_882435 prefixEnd_882435 453113301350360202704261 := by
  unfold tailWord_882435
  simp only [CollatzResearch.WordTrace]
  refine ⟨32185048558096177744640759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21456699038730785163093839 32185048558096177744640759)
  ·
    refine ⟨48277572837144266616961139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32185048558096177744640759 48277572837144266616961139)
    ·
      refine ⟨72416359255716399925441709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48277572837144266616961139 72416359255716399925441709)
      ·
        refine ⟨27156134720893649972040641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72416359255716399925441709 27156134720893649972040641)
        ·
          refine ⟨20367101040670237479030481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27156134720893649972040641 20367101040670237479030481)
          ·
            refine ⟨15275325780502678109272861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20367101040670237479030481 15275325780502678109272861)
            ·
              refine ⟨5728247167688504290977323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15275325780502678109272861 5728247167688504290977323)
              ·
                refine ⟨8592370751532756436465985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5728247167688504290977323 8592370751532756436465985)
                ·
                  refine ⟨6444278063649567327349489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8592370751532756436465985 6444278063649567327349489)
                  ·
                    refine ⟨4833208547737175495512117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6444278063649567327349489 4833208547737175495512117)
                    ·
                      refine ⟨453113301350360202704261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4833208547737175495512117 453113301350360202704261)
                      ·
                        rfl

theorem cell23_882435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 2, 5].length) (baseStart_882435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_882435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_882435 prefixEnd_882435 := by exact prefixLift 882435
  have htrace : WordTrace (prefixWord ++ tailWord_882435) baseStart_882435 baseEnd_882435 := by
    simpa [prefixWord, tailWord_882435, baseEnd_882435] using wordTrace_append hprefix tailTrace_882435
  have hstable : (prefixWord ++ tailWord_882435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882435).length < 2 ^ (prefixWord ++ tailWord_882435).sum := by decide
  have hdescent : baseEnd_882435 < baseStart_882435 := by decide
  rcases family_descends (prefixWord ++ tailWord_882435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882482 : List Nat := [3, 2, 1, 1, 3, 2, 1, 2, 2, 1, 5]
def baseStart_882482 : Nat := 118140960795 + 882482 * 2 ^ 59
def prefixEnd_882482 : Nat := 4983230072969 + 3 ^ 40 * 882482 * 2
def baseEnd_882482 : Nat := 453137434941121518816545

theorem tailTrace_882482 : CollatzResearch.WordTrace tailWord_882482 prefixEnd_882482 453137434941121518816545 := by
  unfold tailWord_882482
  simp only [CollatzResearch.WordTrace]
  refine ⟨8046690697231476192900425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21457841859283936514401133 8046690697231476192900425)
  ·
    refine ⟨6035018022923607144675319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8046690697231476192900425 6035018022923607144675319)
    ·
      refine ⟨9052527034385410717012979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6035018022923607144675319 9052527034385410717012979)
      ·
        refine ⟨13578790551578116075519469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9052527034385410717012979 13578790551578116075519469)
        ·
          refine ⟨5092046456841793528319801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13578790551578116075519469 5092046456841793528319801)
          ·
            refine ⟨3819034842631345146239851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5092046456841793528319801 3819034842631345146239851)
            ·
              refine ⟨5728552263947017719359777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3819034842631345146239851 5728552263947017719359777)
              ·
                refine ⟨4296414197960263289519833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5728552263947017719359777 4296414197960263289519833)
                ·
                  refine ⟨3222310648470197467139875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4296414197960263289519833 3222310648470197467139875)
                  ·
                    refine ⟨4833465972705296200709813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3222310648470197467139875 4833465972705296200709813)
                    ·
                      refine ⟨453137434941121518816545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4833465972705296200709813 453137434941121518816545)
                      ·
                        rfl

theorem cell23_882482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_882482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_882482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_882482 prefixEnd_882482 := by exact prefixLift 882482
  have htrace : WordTrace (prefixWord ++ tailWord_882482) baseStart_882482 baseEnd_882482 := by
    simpa [prefixWord, tailWord_882482, baseEnd_882482] using wordTrace_append hprefix tailTrace_882482
  have hstable : (prefixWord ++ tailWord_882482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882482).length < 2 ^ (prefixWord ++ tailWord_882482).sum := by decide
  have hdescent : baseEnd_882482 < baseStart_882482 := by decide
  rcases family_descends (prefixWord ++ tailWord_882482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882483 : List Nat := [1, 1, 1, 2, 7, 2, 1, 2, 1, 3, 2]
def baseStart_882483 : Nat := 118140960795 + 882483 * 2 ^ 59
def prefixEnd_882483 : Nat := 4983230072969 + 3 ^ 40 * 882483 * 2
def baseEnd_882483 : Nat := 453137948421776014904041

theorem tailTrace_882483 : CollatzResearch.WordTrace tailWord_882483 prefixEnd_882483 453137948421776014904041 := by
  unfold tailWord_882483
  simp only [CollatzResearch.WordTrace]
  refine ⟨32186799261922281942388103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21457866174614854628258735 32186799261922281942388103)
  ·
    refine ⟨48280198892883422913582155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32186799261922281942388103 48280198892883422913582155)
    ·
      refine ⟨72420298339325134370373233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48280198892883422913582155 72420298339325134370373233)
      ·
        refine ⟨54315223754493850777779925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72420298339325134370373233 54315223754493850777779925)
        ·
          refine ⟨1273013056745949627604217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 54315223754493850777779925 1273013056745949627604217)
          ·
            refine ⟨954759792559462220703163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1273013056745949627604217 954759792559462220703163)
            ·
              refine ⟨1432139688839193331054745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 954759792559462220703163 1432139688839193331054745)
              ·
                refine ⟨1074104766629394998291059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1432139688839193331054745 1074104766629394998291059)
                ·
                  refine ⟨1611157149944092497436589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1074104766629394998291059 1611157149944092497436589)
                  ·
                    refine ⟨604183931229034686538721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1611157149944092497436589 604183931229034686538721)
                    ·
                      refine ⟨453137948421776014904041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 604183931229034686538721 453137948421776014904041)
                      ·
                        rfl

theorem cell23_882483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 2, 1, 3, 2].length) (baseStart_882483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_882483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_882483 prefixEnd_882483 := by exact prefixLift 882483
  have htrace : WordTrace (prefixWord ++ tailWord_882483) baseStart_882483 baseEnd_882483 := by
    simpa [prefixWord, tailWord_882483, baseEnd_882483] using wordTrace_append hprefix tailTrace_882483
  have hstable : (prefixWord ++ tailWord_882483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882483).length < 2 ^ (prefixWord ++ tailWord_882483).sum := by decide
  have hdescent : baseEnd_882483 < baseStart_882483 := by decide
  rcases family_descends (prefixWord ++ tailWord_882483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882512 : List Nat := [2, 1, 1, 1, 1, 4, 1, 4, 2, 3, 3]
def baseStart_882512 : Nat := 118140960795 + 882512 * 2 ^ 59
def prefixEnd_882512 : Nat := 4983230072969 + 3 ^ 40 * 882512 * 2
def baseEnd_882512 : Nat := 453152839360756401441407

theorem tailTrace_882512 : CollatzResearch.WordTrace tailWord_882512 prefixEnd_882512 453152839360756401441407 := by
  unfold tailWord_882512
  simp only [CollatzResearch.WordTrace]
  refine ⟨16093928489408609947596895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21458571319211479930129193 16093928489408609947596895)
  ·
    refine ⟨24140892734112914921395343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16093928489408609947596895 24140892734112914921395343)
    ·
      refine ⟨36211339101169372382093015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24140892734112914921395343 36211339101169372382093015)
      ·
        refine ⟨54317008651754058573139523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36211339101169372382093015 54317008651754058573139523)
        ·
          refine ⟨81475512977631087859709285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54317008651754058573139523 81475512977631087859709285)
          ·
            refine ⟨15276658683305828973695491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81475512977631087859709285 15276658683305828973695491)
            ·
              refine ⟨22914988024958743460543237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15276658683305828973695491 22914988024958743460543237)
              ·
                refine ⟨4296560254679764398851857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22914988024958743460543237 4296560254679764398851857)
                ·
                  refine ⟨3222420191009823299138893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4296560254679764398851857 3222420191009823299138893)
                  ·
                    refine ⟨1208407571628683737177085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3222420191009823299138893 1208407571628683737177085)
                    ·
                      refine ⟨453152839360756401441407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1208407571628683737177085 453152839360756401441407)
                      ·
                        rfl

theorem cell23_882512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 2, 3, 3].length) (baseStart_882512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_882512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_882512 prefixEnd_882512 := by exact prefixLift 882512
  have htrace : WordTrace (prefixWord ++ tailWord_882512) baseStart_882512 baseEnd_882512 := by
    simpa [prefixWord, tailWord_882512, baseEnd_882512] using wordTrace_append hprefix tailTrace_882512
  have hstable : (prefixWord ++ tailWord_882512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882512).length < 2 ^ (prefixWord ++ tailWord_882512).sum := by decide
  have hdescent : baseEnd_882512 < baseStart_882512 := by decide
  rcases family_descends (prefixWord ++ tailWord_882512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882513 : List Nat := [1, 2, 2, 1, 5, 2, 2, 2, 2, 2, 2]
def baseStart_882513 : Nat := 118140960795 + 882513 * 2 ^ 59
def prefixEnd_882513 : Nat := 4983230072969 + 3 ^ 40 * 882513 * 2
def baseEnd_882513 : Nat := 453153352841410897528903

theorem tailTrace_882513 : CollatzResearch.WordTrace tailWord_882513 prefixEnd_882513 453153352841410897528903 := by
  unfold tailWord_882513
  simp only [CollatzResearch.WordTrace]
  refine ⟨32187893451813597065980193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21458595634542398043986795 32187893451813597065980193)
  ·
    refine ⟨24140920088860197799485145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32187893451813597065980193 24140920088860197799485145)
    ·
      refine ⟨18105690066645148349613859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24140920088860197799485145 18105690066645148349613859)
      ·
        refine ⟨27158535099967722524420789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18105690066645148349613859 27158535099967722524420789)
        ·
          refine ⟨2546112665621973986664449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27158535099967722524420789 2546112665621973986664449)
          ·
            refine ⟨1909584499216480489998337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2546112665621973986664449 1909584499216480489998337)
            ·
              refine ⟨1432188374412360367498753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1909584499216480489998337 1432188374412360367498753)
              ·
                refine ⟨1074141280809270275624065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1432188374412360367498753 1074141280809270275624065)
                ·
                  refine ⟨805605960606952706718049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1074141280809270275624065 805605960606952706718049)
                  ·
                    refine ⟨604204470455214530038537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 805605960606952706718049 604204470455214530038537)
                    ·
                      refine ⟨453153352841410897528903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 604204470455214530038537 453153352841410897528903)
                      ·
                        rfl

theorem cell23_882513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 2, 2, 2, 2].length) (baseStart_882513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_882513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_882513 prefixEnd_882513 := by exact prefixLift 882513
  have htrace : WordTrace (prefixWord ++ tailWord_882513) baseStart_882513 baseEnd_882513 := by
    simpa [prefixWord, tailWord_882513, baseEnd_882513] using wordTrace_append hprefix tailTrace_882513
  have hstable : (prefixWord ++ tailWord_882513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882513).length < 2 ^ (prefixWord ++ tailWord_882513).sum := by decide
  have hdescent : baseEnd_882513 < baseStart_882513 := by decide
  rcases family_descends (prefixWord ++ tailWord_882513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882515 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 5, 7]
def baseStart_882515 : Nat := 118140960795 + 882515 * 2 ^ 59
def prefixEnd_882515 : Nat := 4983230072969 + 3 ^ 40 * 882515 * 2
def baseEnd_882515 : Nat := 151051459934239963234631

theorem tailTrace_882515 : CollatzResearch.WordTrace tailWord_882515 prefixEnd_882515 151051459934239963234631 := by
  unfold tailWord_882515
  simp only [CollatzResearch.WordTrace]
  refine ⟨32187966397806351407552999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21458644265204234271701999 32187966397806351407552999)
  ·
    refine ⟨48281949596709527111329499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32187966397806351407552999 48281949596709527111329499)
    ·
      refine ⟨72422924395064290666994249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48281949596709527111329499 72422924395064290666994249)
      ·
        refine ⟨54317193296298218000245687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72422924395064290666994249 54317193296298218000245687)
        ·
          refine ⟨81475789944447327000368531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54317193296298218000245687 81475789944447327000368531)
          ·
            refine ⟨122213684916670990500552797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81475789944447327000368531 122213684916670990500552797)
            ·
              refine ⟨45830131843751621437707299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122213684916670990500552797 45830131843751621437707299)
              ·
                refine ⟨68745197765627432156560949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45830131843751621437707299 68745197765627432156560949)
                ·
                  refine ⟨6444862290527571764677589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68745197765627432156560949 6444862290527571764677589)
                  ·
                    refine ⟨151051459934239963234631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6444862290527571764677589 151051459934239963234631)
                    ·
                      rfl

theorem cell23_882515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 7].length) (baseStart_882515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_882515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_882515 prefixEnd_882515 := by exact prefixLift 882515
  have htrace : WordTrace (prefixWord ++ tailWord_882515) baseStart_882515 baseEnd_882515 := by
    simpa [prefixWord, tailWord_882515, baseEnd_882515] using wordTrace_append hprefix tailTrace_882515
  have hstable : (prefixWord ++ tailWord_882515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882515).length < 2 ^ (prefixWord ++ tailWord_882515).sum := by decide
  have hdescent : baseEnd_882515 < baseStart_882515 := by decide
  rcases family_descends (prefixWord ++ tailWord_882515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882569 : List Nat := [1, 2, 1, 1, 5, 1, 1, 1, 4, 4, 2]
def baseStart_882569 : Nat := 118140960795 + 882569 * 2 ^ 59
def prefixEnd_882569 : Nat := 4983230072969 + 3 ^ 40 * 882569 * 2
def baseEnd_882569 : Nat := 453182107758062678428645

theorem tailTrace_882569 : CollatzResearch.WordTrace tailWord_882569 prefixEnd_882569 453182107758062678428645 := by
  unfold tailWord_882569
  simp only [CollatzResearch.WordTrace]
  refine ⟨32189935939610718630018761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21459957293073812420012507 32189935939610718630018761)
  ·
    refine ⟨24142451954708038972514071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32189935939610718630018761 24142451954708038972514071)
    ·
      refine ⟨36213677932062058458771107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24142451954708038972514071 36213677932062058458771107)
      ·
        refine ⟨54320516898093087688156661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36213677932062058458771107 54320516898093087688156661)
        ·
          refine ⟨5092548459196226970764687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54320516898093087688156661 5092548459196226970764687)
          ·
            refine ⟨7638822688794340456147031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5092548459196226970764687 7638822688794340456147031)
            ·
              refine ⟨11458234033191510684220547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7638822688794340456147031 11458234033191510684220547)
              ·
                refine ⟨17187351049787266026330821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11458234033191510684220547 17187351049787266026330821)
                ·
                  refine ⟨3222628321835112379937029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17187351049787266026330821 3222628321835112379937029)
                  ·
                    refine ⟨604242810344083571238193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3222628321835112379937029 604242810344083571238193)
                    ·
                      refine ⟨453182107758062678428645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 604242810344083571238193 453182107758062678428645)
                      ·
                        rfl

theorem cell23_882569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 4, 4, 2].length) (baseStart_882569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_882569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_882569 prefixEnd_882569 := by exact prefixLift 882569
  have htrace : WordTrace (prefixWord ++ tailWord_882569) baseStart_882569 baseEnd_882569 := by
    simpa [prefixWord, tailWord_882569, baseEnd_882569] using wordTrace_append hprefix tailTrace_882569
  have hstable : (prefixWord ++ tailWord_882569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882569).length < 2 ^ (prefixWord ++ tailWord_882569).sum := by decide
  have hdescent : baseEnd_882569 < baseStart_882569 := by decide
  rcases family_descends (prefixWord ++ tailWord_882569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882586 : List Nat := [3, 1, 1, 4, 2, 1, 2, 1, 2, 4, 2]
def baseStart_882586 : Nat := 118140960795 + 882586 * 2 ^ 59
def prefixEnd_882586 : Nat := 4983230072969 + 3 ^ 40 * 882586 * 2
def baseEnd_882586 : Nat := 453190836929189111916067

theorem tailTrace_882586 : CollatzResearch.WordTrace tailWord_882586 prefixEnd_882586 453190836929189111916067 := by
  unfold tailWord_882586
  simp only [CollatzResearch.WordTrace]
  refine ⟨8047638995137282633346903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21460370653699420355591741 8047638995137282633346903)
  ·
    refine ⟨12071458492705923950020355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8047638995137282633346903 12071458492705923950020355)
    ·
      refine ⟨18107187739058885925030533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12071458492705923950020355 18107187739058885925030533)
      ·
        refine ⟨3395097701073541110943225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18107187739058885925030533 3395097701073541110943225)
        ·
          refine ⟨2546323275805155833207419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3395097701073541110943225 2546323275805155833207419)
          ·
            refine ⟨3819484913707733749811129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2546323275805155833207419 3819484913707733749811129)
            ·
              refine ⟨2864613685280800312358347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3819484913707733749811129 2864613685280800312358347)
              ·
                refine ⟨4296920527921200468537521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2864613685280800312358347 4296920527921200468537521)
                ·
                  refine ⟨3222690395940900351403141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4296920527921200468537521 3222690395940900351403141)
                  ·
                    refine ⟨604254449238918815888089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3222690395940900351403141 604254449238918815888089)
                    ·
                      refine ⟨453190836929189111916067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 604254449238918815888089 453190836929189111916067)
                      ·
                        rfl

theorem cell23_882586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_882586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_882586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_882586 prefixEnd_882586 := by exact prefixLift 882586
  have htrace : WordTrace (prefixWord ++ tailWord_882586) baseStart_882586 baseEnd_882586 := by
    simpa [prefixWord, tailWord_882586, baseEnd_882586] using wordTrace_append hprefix tailTrace_882586
  have hstable : (prefixWord ++ tailWord_882586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882586).length < 2 ^ (prefixWord ++ tailWord_882586).sum := by decide
  have hdescent : baseEnd_882586 < baseStart_882586 := by decide
  rcases family_descends (prefixWord ++ tailWord_882586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882589 : List Nat := [1, 4, 2, 1, 2, 2, 1, 2, 1, 4, 3]
def baseStart_882589 : Nat := 118140960795 + 882589 * 2 ^ 59
def prefixEnd_882589 : Nat := 4983230072969 + 3 ^ 40 * 882589 * 2
def baseEnd_882589 : Nat := 453192377371152600178553

theorem tailTrace_882589 : CollatzResearch.WordTrace tailWord_882589 prefixEnd_882589 453192377371152600178553 := by
  unfold tailWord_882589
  simp only [CollatzResearch.WordTrace]
  refine ⟨32190665399538262045746821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21460443599692174697164547 32190665399538262045746821)
  ·
    refine ⟨6035749762413424133577529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32190665399538262045746821 6035749762413424133577529)
    ·
      refine ⟨4526812321810068100183147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6035749762413424133577529 4526812321810068100183147)
      ·
        refine ⟨6790218482715102150274721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4526812321810068100183147 6790218482715102150274721)
        ·
          refine ⟨5092663862036326612706041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6790218482715102150274721 5092663862036326612706041)
          ·
            refine ⟨3819497896527244959529531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5092663862036326612706041 3819497896527244959529531)
            ·
              refine ⟨5729246844790867439294297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3819497896527244959529531 5729246844790867439294297)
              ·
                refine ⟨4296935133593150579470723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5729246844790867439294297 4296935133593150579470723)
                ·
                  refine ⟨6445402700389725869206085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4296935133593150579470723 6445402700389725869206085)
                  ·
                    refine ⟨1208513006323073600476141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6445402700389725869206085 1208513006323073600476141)
                    ·
                      refine ⟨453192377371152600178553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1208513006323073600476141 453192377371152600178553)
                      ·
                        rfl

theorem cell23_882589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_882589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_882589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_882589 prefixEnd_882589 := by exact prefixLift 882589
  have htrace : WordTrace (prefixWord ++ tailWord_882589) baseStart_882589 baseEnd_882589 := by
    simpa [prefixWord, tailWord_882589, baseEnd_882589] using wordTrace_append hprefix tailTrace_882589
  have hstable : (prefixWord ++ tailWord_882589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882589).length < 2 ^ (prefixWord ++ tailWord_882589).sum := by decide
  have hdescent : baseEnd_882589 < baseStart_882589 := by decide
  rcases family_descends (prefixWord ++ tailWord_882589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882613 : List Nat := [1, 3, 3, 2, 1, 2, 3, 3, 1, 4]
def baseStart_882613 : Nat := 118140960795 + 882613 * 2 ^ 59
def prefixEnd_882613 : Nat := 4983230072969 + 3 ^ 40 * 882613 * 2
def baseEnd_882613 : Nat := 151068233635620168759481

theorem tailTrace_882613 : CollatzResearch.WordTrace tailWord_882613 prefixEnd_882613 151068233635620168759481 := by
  unfold tailWord_882613
  simp only [CollatzResearch.WordTrace]
  refine ⟨32191540751451314144620493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21461027167634209429746995 32191540751451314144620493)
  ·
    refine ⟨12071827781794242804232685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32191540751451314144620493 12071827781794242804232685)
    ·
      refine ⟨4526935418172841051587257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12071827781794242804232685 4526935418172841051587257)
      ·
        refine ⟨3395201563629630788690443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4526935418172841051587257 3395201563629630788690443)
        ·
          refine ⟨5092802345444446183035665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3395201563629630788690443 5092802345444446183035665)
          ·
            refine ⟨3819601759083334637276749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5092802345444446183035665 3819601759083334637276749)
            ·
              refine ⟨1432350659656250488978781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3819601759083334637276749 1432350659656250488978781)
              ·
                refine ⟨537131497371093933367043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1432350659656250488978781 537131497371093933367043)
                ·
                  refine ⟨805697246056640900050565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 537131497371093933367043 805697246056640900050565)
                  ·
                    refine ⟨151068233635620168759481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 805697246056640900050565 151068233635620168759481)
                    ·
                      rfl

theorem cell23_882613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 3, 1, 4].length) (baseStart_882613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_882613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_882613 prefixEnd_882613 := by exact prefixLift 882613
  have htrace : WordTrace (prefixWord ++ tailWord_882613) baseStart_882613 baseEnd_882613 := by
    simpa [prefixWord, tailWord_882613, baseEnd_882613] using wordTrace_append hprefix tailTrace_882613
  have hstable : (prefixWord ++ tailWord_882613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882613).length < 2 ^ (prefixWord ++ tailWord_882613).sum := by decide
  have hdescent : baseEnd_882613 < baseStart_882613 := by decide
  rcases family_descends (prefixWord ++ tailWord_882613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882619 : List Nat := [1, 1, 1, 1, 1, 2, 2, 3, 7, 1, 3]
def baseStart_882619 : Nat := 118140960795 + 882619 * 2 ^ 59
def prefixEnd_882619 : Nat := 4983230072969 + 3 ^ 40 * 882619 * 2
def baseEnd_882619 : Nat := 453207781790787482803415

theorem tailTrace_882619 : CollatzResearch.WordTrace tailWord_882619 prefixEnd_882619 453207781790787482803415 := by
  unfold tailWord_882619
  simp only [CollatzResearch.WordTrace]
  refine ⟨32191759589429577169338911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21461173059619718112892607 32191759589429577169338911)
  ·
    refine ⟨48287639384144365754008367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32191759589429577169338911 48287639384144365754008367)
    ·
      refine ⟨72431459076216548631012551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48287639384144365754008367 72431459076216548631012551)
      ·
        refine ⟨108647188614324822946518827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72431459076216548631012551 108647188614324822946518827)
        ·
          refine ⟨162970782921487234419778241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108647188614324822946518827 162970782921487234419778241)
          ·
            refine ⟨122228087191115425814833681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162970782921487234419778241 122228087191115425814833681)
            ·
              refine ⟨91671065393336569361125261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122228087191115425814833681 91671065393336569361125261)
              ·
                refine ⟨34376649522501213510421973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91671065393336569361125261 34376649522501213510421973)
                ·
                  refine ⟨805702723183622191650515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 34376649522501213510421973 805702723183622191650515)
                  ·
                    refine ⟨1208554084775433287475773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 805702723183622191650515 1208554084775433287475773)
                    ·
                      refine ⟨453207781790787482803415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1208554084775433287475773 453207781790787482803415)
                      ·
                        rfl

theorem cell23_882619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 7, 1, 3].length) (baseStart_882619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_882619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_882619 prefixEnd_882619 := by exact prefixLift 882619
  have htrace : WordTrace (prefixWord ++ tailWord_882619) baseStart_882619 baseEnd_882619 := by
    simpa [prefixWord, tailWord_882619, baseEnd_882619] using wordTrace_append hprefix tailTrace_882619
  have hstable : (prefixWord ++ tailWord_882619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882619).length < 2 ^ (prefixWord ++ tailWord_882619).sum := by decide
  have hdescent : baseEnd_882619 < baseStart_882619 := by decide
  rcases family_descends (prefixWord ++ tailWord_882619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882629 : List Nat := [1, 3, 1, 1, 1, 1, 1, 4, 3, 5, 2]
def baseStart_882629 : Nat := 118140960795 + 882629 * 2 ^ 59
def prefixEnd_882629 : Nat := 4983230072969 + 3 ^ 40 * 882629 * 2
def baseEnd_882629 : Nat := 453212916597332443678369

theorem tailTrace_882629 : CollatzResearch.WordTrace tailWord_882629 prefixEnd_882629 453212916597332443678369 := by
  unfold tailWord_882629
  simp only [CollatzResearch.WordTrace]
  refine ⟨32192124319393348877202941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21461416212928899251468627 32192124319393348877202941)
  ·
    refine ⟨12072046619772505828951103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32192124319393348877202941 12072046619772505828951103)
    ·
      refine ⟨18108069929658758743426655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12072046619772505828951103 18108069929658758743426655)
      ·
        refine ⟨27162104894488138115139983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18108069929658758743426655 27162104894488138115139983)
        ·
          refine ⟨40743157341732207172709975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27162104894488138115139983 40743157341732207172709975)
          ·
            refine ⟨61114736012598310759064963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40743157341732207172709975 61114736012598310759064963)
            ·
              refine ⟨91672104018897466138597445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61114736012598310759064963 91672104018897466138597445)
              ·
                refine ⟨17188519503543274900987021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91672104018897466138597445 17188519503543274900987021)
                ·
                  refine ⟨6445694813828728087870133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17188519503543274900987021 6445694813828728087870133)
                  ·
                    refine ⟨604283888796443258237825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6445694813828728087870133 604283888796443258237825)
                    ·
                      refine ⟨453212916597332443678369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 604283888796443258237825 453212916597332443678369)
                      ·
                        rfl

theorem cell23_882629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 5, 2].length) (baseStart_882629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_882629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_882629 prefixEnd_882629 := by exact prefixLift 882629
  have htrace : WordTrace (prefixWord ++ tailWord_882629) baseStart_882629 baseEnd_882629 := by
    simpa [prefixWord, tailWord_882629, baseEnd_882629] using wordTrace_append hprefix tailTrace_882629
  have hstable : (prefixWord ++ tailWord_882629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882629).length < 2 ^ (prefixWord ++ tailWord_882629).sum := by decide
  have hdescent : baseEnd_882629 < baseStart_882629 := by decide
  rcases family_descends (prefixWord ++ tailWord_882629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882673 : List Nat := [1, 2, 2, 2, 5, 1, 3, 1, 1, 5]
def baseStart_882673 : Nat := 118140960795 + 882673 * 2 ^ 59
def prefixEnd_882673 : Nat := 4983230072969 + 3 ^ 40 * 882673 * 2
def baseEnd_882673 : Nat := 151078503248710090509389

theorem tailTrace_882673 : CollatzResearch.WordTrace tailWord_882673 prefixEnd_882673 151078503248710090509389 := by
  unfold tailWord_882673
  simp only [CollatzResearch.WordTrace]
  refine ⟨32193729131233944391804673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21462486087489296261203115 32193729131233944391804673)
  ·
    refine ⟨24145296848425458293853505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32193729131233944391804673 24145296848425458293853505)
    ·
      refine ⟨18108972636319093720390129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24145296848425458293853505 18108972636319093720390129)
      ·
        refine ⟨13581729477239320290292597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18108972636319093720390129 13581729477239320290292597)
        ·
          refine ⟨1273287138491186277214931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13581729477239320290292597 1273287138491186277214931)
          ·
            refine ⟨1909930707736779415822397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1273287138491186277214931 1909930707736779415822397)
            ·
              refine ⟨716224015401292280933399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1909930707736779415822397 716224015401292280933399)
              ·
                refine ⟨1074336023101938421400099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 716224015401292280933399 1074336023101938421400099)
                ·
                  refine ⟨1611504034652907632100149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1074336023101938421400099 1611504034652907632100149)
                  ·
                    refine ⟨151078503248710090509389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1611504034652907632100149 151078503248710090509389)
                    ·
                      rfl

theorem cell23_882673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 3, 1, 1, 5].length) (baseStart_882673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_882673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_882673 prefixEnd_882673 := by exact prefixLift 882673
  have htrace : WordTrace (prefixWord ++ tailWord_882673) baseStart_882673 baseEnd_882673 := by
    simpa [prefixWord, tailWord_882673, baseEnd_882673] using wordTrace_append hprefix tailTrace_882673
  have hstable : (prefixWord ++ tailWord_882673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882673).length < 2 ^ (prefixWord ++ tailWord_882673).sum := by decide
  have hdescent : baseEnd_882673 < baseStart_882673 := by decide
  rcases family_descends (prefixWord ++ tailWord_882673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882689 : List Nat := [1, 2, 4, 1, 2, 1, 1, 2, 3, 2, 4]
def baseStart_882689 : Nat := 118140960795 + 882689 * 2 ^ 59
def prefixEnd_882689 : Nat := 4983230072969 + 3 ^ 40 * 882689 * 2
def baseEnd_882689 : Nat := 453243725436602208928093

theorem tailTrace_882689 : CollatzResearch.WordTrace tailWord_882689 prefixEnd_882689 453243725436602208928093 := by
  unfold tailWord_882689
  simp only [CollatzResearch.WordTrace]
  refine ⟨32194312699175979124387121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21462875132783986082924747 32194312699175979124387121)
  ·
    refine ⟨24145734524381984343290341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32194312699175979124387121 24145734524381984343290341)
    ·
      refine ⟨4527325223321622064366939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24145734524381984343290341 4527325223321622064366939)
      ·
        refine ⟨6790987834982433096550409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4527325223321622064366939 6790987834982433096550409)
        ·
          refine ⟨5093240876236824822412807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6790987834982433096550409 5093240876236824822412807)
          ·
            refine ⟨7639861314355237233619211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5093240876236824822412807 7639861314355237233619211)
            ·
              refine ⟨11459791971532855850428817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7639861314355237233619211 11459791971532855850428817)
              ·
                refine ⟨8594843978649641887821613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11459791971532855850428817 8594843978649641887821613)
                ·
                  refine ⟨3223066491993615707933105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8594843978649641887821613 3223066491993615707933105)
                  ·
                    refine ⟨2417299868995211780949829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3223066491993615707933105 2417299868995211780949829)
                    ·
                      refine ⟨453243725436602208928093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2417299868995211780949829 453243725436602208928093)
                      ·
                        rfl

theorem cell23_882689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_882689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_882689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_882689 prefixEnd_882689 := by exact prefixLift 882689
  have htrace : WordTrace (prefixWord ++ tailWord_882689) baseStart_882689 baseEnd_882689 := by
    simpa [prefixWord, tailWord_882689, baseEnd_882689] using wordTrace_append hprefix tailTrace_882689
  have hstable : (prefixWord ++ tailWord_882689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882689).length < 2 ^ (prefixWord ++ tailWord_882689).sum := by decide
  have hdescent : baseEnd_882689 < baseStart_882689 := by decide
  rcases family_descends (prefixWord ++ tailWord_882689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882716 : List Nat := [2, 2, 3, 1, 3, 2, 3, 7]
def baseStart_882716 : Nat := 118140960795 + 882716 * 2 ^ 59
def prefixEnd_882716 : Nat := 4983230072969 + 3 ^ 40 * 882716 * 2
def baseEnd_882716 : Nat := 16787318126454577899647

theorem tailTrace_882716 : CollatzResearch.WordTrace tailWord_882716 prefixEnd_882716 16787318126454577899647 := by
  unfold tailWord_882716
  simp only [CollatzResearch.WordTrace]
  refine ⟨16097648735039081367810001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21463531646718775157080001 16097648735039081367810001)
  ·
    refine ⟨12073236551279311025857501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16097648735039081367810001 12073236551279311025857501)
    ·
      refine ⟨4527463706729741634696563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12073236551279311025857501 4527463706729741634696563)
      ·
        refine ⟨6791195560094612452044845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4527463706729741634696563 6791195560094612452044845)
        ·
          refine ⟨2546698335035479669516817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6791195560094612452044845 2546698335035479669516817)
          ·
            refine ⟨1910023751276609752137613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2546698335035479669516817 1910023751276609752137613)
            ·
              refine ⟨716258906728728657051605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1910023751276609752137613 716258906728728657051605)
              ·
                refine ⟨16787318126454577899647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 716258906728728657051605 16787318126454577899647)
                ·
                  rfl

theorem cell23_882716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 3, 7].length) (baseStart_882716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_882716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_882716 prefixEnd_882716 := by exact prefixLift 882716
  have htrace : WordTrace (prefixWord ++ tailWord_882716) baseStart_882716 baseEnd_882716 := by
    simpa [prefixWord, tailWord_882716, baseEnd_882716] using wordTrace_append hprefix tailTrace_882716
  have hstable : (prefixWord ++ tailWord_882716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882716).length < 2 ^ (prefixWord ++ tailWord_882716).sum := by decide
  have hdescent : baseEnd_882716 < baseStart_882716 := by decide
  rcases family_descends (prefixWord ++ tailWord_882716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882727 : List Nat := [1, 1, 7, 1, 2, 2, 2, 1, 1, 1, 4]
def baseStart_882727 : Nat := 118140960795 + 882727 * 2 ^ 59
def prefixEnd_882727 : Nat := 4983230072969 + 3 ^ 40 * 882727 * 2
def baseEnd_882727 : Nat := 453263237701473060252919

theorem tailTrace_882727 : CollatzResearch.WordTrace tailWord_882727 prefixEnd_882727 453263237701473060252919 := by
  unfold tailWord_882727
  simp only [CollatzResearch.WordTrace]
  refine ⟨32195698673038311614270435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21463799115358874409513623 32195698673038311614270435)
  ·
    refine ⟨48293548009557467421405653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32195698673038311614270435 48293548009557467421405653)
    ·
      refine ⟨1131880031474003142689195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 48293548009557467421405653 1131880031474003142689195)
      ·
        refine ⟨1697820047211004714033793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1131880031474003142689195 1697820047211004714033793)
        ·
          refine ⟨1273365035408253535525345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1697820047211004714033793 1273365035408253535525345)
          ·
            refine ⟨955023776556190151644009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1273365035408253535525345 955023776556190151644009)
            ·
              refine ⟨716267832417142613733007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 955023776556190151644009 716267832417142613733007)
              ·
                refine ⟨1074401748625713920599511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 716267832417142613733007 1074401748625713920599511)
                ·
                  refine ⟨1611602622938570880899267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1074401748625713920599511 1611602622938570880899267)
                  ·
                    refine ⟨2417403934407856321348901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1611602622938570880899267 2417403934407856321348901)
                    ·
                      refine ⟨453263237701473060252919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2417403934407856321348901 453263237701473060252919)
                      ·
                        rfl

theorem cell23_882727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_882727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_882727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_882727 prefixEnd_882727 := by exact prefixLift 882727
  have htrace : WordTrace (prefixWord ++ tailWord_882727) baseStart_882727 baseEnd_882727 := by
    simpa [prefixWord, tailWord_882727, baseEnd_882727] using wordTrace_append hprefix tailTrace_882727
  have hstable : (prefixWord ++ tailWord_882727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882727).length < 2 ^ (prefixWord ++ tailWord_882727).sum := by decide
  have hdescent : baseEnd_882727 < baseStart_882727 := by decide
  rcases family_descends (prefixWord ++ tailWord_882727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882730 : List Nat := [3, 1, 4, 1, 2, 1, 4, 1, 1, 2, 3]
def baseStart_882730 : Nat := 118140960795 + 882730 * 2 ^ 59
def prefixEnd_882730 : Nat := 4983230072969 + 3 ^ 40 * 882730 * 2
def baseEnd_882730 : Nat := 453264778143436548515405

theorem tailTrace_882730 : CollatzResearch.WordTrace tailWord_882730 prefixEnd_882730 453264778143436548515405 := by
  unfold tailWord_882730
  simp only [CollatzResearch.WordTrace]
  refine ⟨8048952023006860781657411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21463872061351628751086429 8048952023006860781657411)
  ·
    refine ⟨12073428034510291172486117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8048952023006860781657411 12073428034510291172486117)
    ·
      refine ⟨2263767756470679594841147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12073428034510291172486117 2263767756470679594841147)
      ·
        refine ⟨3395651634706019392261721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2263767756470679594841147 3395651634706019392261721)
        ·
          refine ⟨2546738726029514544196291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3395651634706019392261721 2546738726029514544196291)
          ·
            refine ⟨3820108089044271816294437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2546738726029514544196291 3820108089044271816294437)
            ·
              refine ⟨716270266695800965555207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3820108089044271816294437 716270266695800965555207)
              ·
                refine ⟨1074405400043701448332811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 716270266695800965555207 1074405400043701448332811)
                ·
                  refine ⟨1611608100065552172499217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1074405400043701448332811 1611608100065552172499217)
                  ·
                    refine ⟨1208706075049164129374413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1611608100065552172499217 1208706075049164129374413)
                    ·
                      refine ⟨453264778143436548515405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1208706075049164129374413 453264778143436548515405)
                      ·
                        rfl

theorem cell23_882730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_882730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_882730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_882730 prefixEnd_882730 := by exact prefixLift 882730
  have htrace : WordTrace (prefixWord ++ tailWord_882730) baseStart_882730 baseEnd_882730 := by
    simpa [prefixWord, tailWord_882730, baseEnd_882730] using wordTrace_append hprefix tailTrace_882730
  have hstable : (prefixWord ++ tailWord_882730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882730).length < 2 ^ (prefixWord ++ tailWord_882730).sum := by decide
  have hdescent : baseEnd_882730 < baseStart_882730 := by decide
  rcases family_descends (prefixWord ++ tailWord_882730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882743 : List Nat := [1, 1, 3, 1, 2, 2, 5, 2, 2, 1, 3]
def baseStart_882743 : Nat := 118140960795 + 882743 * 2 ^ 59
def prefixEnd_882743 : Nat := 4983230072969 + 3 ^ 40 * 882743 * 2
def baseEnd_882743 : Nat := 453271453391944997652845

theorem tailTrace_882743 : CollatzResearch.WordTrace tailWord_882743 prefixEnd_882743 453271453391944997652845 := by
  unfold tailWord_882743
  simp only [CollatzResearch.WordTrace]
  refine ⟨32196282240980346346852883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21464188160653564231235255 32196282240980346346852883)
  ·
    refine ⟨48294423361470519520279325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32196282240980346346852883 48294423361470519520279325)
    ·
      refine ⟨18110408760551444820104747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48294423361470519520279325 18110408760551444820104747)
      ·
        refine ⟨27165613140827167230157121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18110408760551444820104747 27165613140827167230157121)
        ·
          refine ⟨20374209855620375422617841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27165613140827167230157121 20374209855620375422617841)
          ·
            refine ⟨15280657391715281566963381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20374209855620375422617841 15280657391715281566963381)
            ·
              refine ⟨1432561630473307646902817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15280657391715281566963381 1432561630473307646902817)
              ·
                refine ⟨1074421222854980735177113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1432561630473307646902817 1074421222854980735177113)
                ·
                  refine ⟨805815917141235551382835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1074421222854980735177113 805815917141235551382835)
                  ·
                    refine ⟨1208723875711853327074253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 805815917141235551382835 1208723875711853327074253)
                    ·
                      refine ⟨453271453391944997652845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1208723875711853327074253 453271453391944997652845)
                      ·
                        rfl

theorem cell23_882743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 2, 2, 1, 3].length) (baseStart_882743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_882743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_882743 prefixEnd_882743 := by exact prefixLift 882743
  have htrace : WordTrace (prefixWord ++ tailWord_882743) baseStart_882743 baseEnd_882743 := by
    simpa [prefixWord, tailWord_882743, baseEnd_882743] using wordTrace_append hprefix tailTrace_882743
  have hstable : (prefixWord ++ tailWord_882743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882743).length < 2 ^ (prefixWord ++ tailWord_882743).sum := by decide
  have hdescent : baseEnd_882743 < baseStart_882743 := by decide
  rcases family_descends (prefixWord ++ tailWord_882743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882759 : List Nat := [1, 1, 4, 1, 3, 1, 1, 3, 2, 6]
def baseStart_882759 : Nat := 118140960795 + 882759 * 2 ^ 59
def prefixEnd_882759 : Nat := 4983230072969 + 3 ^ 40 * 882759 * 2
def baseEnd_882759 : Nat := 151093223027472311684257

theorem tailTrace_882759 : CollatzResearch.WordTrace tailWord_882759 prefixEnd_882759 151093223027472311684257 := by
  unfold tailWord_882759
  simp only [CollatzResearch.WordTrace]
  refine ⟨32196865808922381079435331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21464577205948254052956887 32196865808922381079435331)
  ·
    refine ⟨48295298713383571619152997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32196865808922381079435331 48295298713383571619152997)
    ·
      refine ⟨9055368508759419678591187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48295298713383571619152997 9055368508759419678591187)
      ·
        refine ⟨13583052763139129517886781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9055368508759419678591187 13583052763139129517886781)
        ·
          refine ⟨5093644786177173569207543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13583052763139129517886781 5093644786177173569207543)
          ·
            refine ⟨7640467179265760353811315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5093644786177173569207543 7640467179265760353811315)
            ·
              refine ⟨11460700768898640530716973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7640467179265760353811315 11460700768898640530716973)
              ·
                refine ⟨4297762788336990199018865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11460700768898640530716973 4297762788336990199018865)
                ·
                  refine ⟨3223322091252742649264149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4297762788336990199018865 3223322091252742649264149)
                  ·
                    refine ⟨151093223027472311684257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3223322091252742649264149 151093223027472311684257)
                    ·
                      rfl

theorem cell23_882759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 2, 6].length) (baseStart_882759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_882759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_882759 prefixEnd_882759 := by exact prefixLift 882759
  have htrace : WordTrace (prefixWord ++ tailWord_882759) baseStart_882759 baseEnd_882759 := by
    simpa [prefixWord, tailWord_882759, baseEnd_882759] using wordTrace_append hprefix tailTrace_882759
  have hstable : (prefixWord ++ tailWord_882759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882759).length < 2 ^ (prefixWord ++ tailWord_882759).sum := by decide
  have hdescent : baseEnd_882759 < baseStart_882759 := by decide
  rcases family_descends (prefixWord ++ tailWord_882759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882769 : List Nat := [1, 2, 2, 1, 3, 1, 1, 4, 2, 1, 5]
def baseStart_882769 : Nat := 118140960795 + 882769 * 2 ^ 59
def prefixEnd_882769 : Nat := 4983230072969 + 3 ^ 40 * 882769 * 2
def baseEnd_882769 : Nat := 453284803888961895927725

theorem tailTrace_882769 : CollatzResearch.WordTrace tailWord_882769 prefixEnd_882769 453284803888961895927725 := by
  unfold tailWord_882769
  simp only [CollatzResearch.WordTrace]
  refine ⟨32197230538886152787299361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21464820359257435191532907 32197230538886152787299361)
  ·
    refine ⟨24147922904164614590474521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32197230538886152787299361 24147922904164614590474521)
    ·
      refine ⟨18110942178123460942855891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24147922904164614590474521 18110942178123460942855891)
      ·
        refine ⟨27166413267185191414283837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18110942178123460942855891 27166413267185191414283837)
        ·
          refine ⟨10187404975194446780356439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27166413267185191414283837 10187404975194446780356439)
          ·
            refine ⟨15281107462791670170534659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10187404975194446780356439 15281107462791670170534659)
            ·
              refine ⟨22921661194187505255801989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15281107462791670170534659 22921661194187505255801989)
              ·
                refine ⟨4297811473910157235462873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22921661194187505255801989 4297811473910157235462873)
                ·
                  refine ⟨3223358605432617926597155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4297811473910157235462873 3223358605432617926597155)
                  ·
                    refine ⟨4835037908148926889895733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3223358605432617926597155 4835037908148926889895733)
                    ·
                      refine ⟨453284803888961895927725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4835037908148926889895733 453284803888961895927725)
                      ·
                        rfl

theorem cell23_882769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 2, 1, 5].length) (baseStart_882769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_882769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_882769 prefixEnd_882769 := by exact prefixLift 882769
  have htrace : WordTrace (prefixWord ++ tailWord_882769) baseStart_882769 baseEnd_882769 := by
    simpa [prefixWord, tailWord_882769, baseEnd_882769] using wordTrace_append hprefix tailTrace_882769
  have hstable : (prefixWord ++ tailWord_882769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882769).length < 2 ^ (prefixWord ++ tailWord_882769).sum := by decide
  have hdescent : baseEnd_882769 < baseStart_882769 := by decide
  rcases family_descends (prefixWord ++ tailWord_882769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882817 : List Nat := [1, 2, 4, 2, 3, 1, 1, 3, 2, 2, 2]
def baseStart_882817 : Nat := 118140960795 + 882817 * 2 ^ 59
def prefixEnd_882817 : Nat := 4983230072969 + 3 ^ 40 * 882817 * 2
def baseEnd_882817 : Nat := 453309450960377708127505

theorem tailTrace_882817 : CollatzResearch.WordTrace tailWord_882817 prefixEnd_882817 453309450960377708127505 := by
  unfold tailWord_882817
  simp only [CollatzResearch.WordTrace]
  refine ⟨32198981242712256985046705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21465987495141504656697803 32198981242712256985046705)
  ·
    refine ⟨24149235932034192738785029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32198981242712256985046705 24149235932034192738785029)
    ·
      refine ⟨4527981737256411138522193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24149235932034192738785029 4527981737256411138522193)
      ·
        refine ⟨3395986302942308353891645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4527981737256411138522193 3395986302942308353891645)
        ·
          refine ⟨1273494863603365632709367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3395986302942308353891645 1273494863603365632709367)
          ·
            refine ⟨1910242295405048449064051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1273494863603365632709367 1910242295405048449064051)
            ·
              refine ⟨2865363443107572673596077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1910242295405048449064051 2865363443107572673596077)
              ·
                refine ⟨1074511291165339752598529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2865363443107572673596077 1074511291165339752598529)
                ·
                  refine ⟨805883468374004814448897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1074511291165339752598529 805883468374004814448897)
                  ·
                    refine ⟨604412601280503610836673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 805883468374004814448897 604412601280503610836673)
                    ·
                      refine ⟨453309450960377708127505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 604412601280503610836673 453309450960377708127505)
                      ·
                        rfl

theorem cell23_882817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_882817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_882817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_882817 prefixEnd_882817 := by exact prefixLift 882817
  have htrace : WordTrace (prefixWord ++ tailWord_882817) baseStart_882817 baseEnd_882817 := by
    simpa [prefixWord, tailWord_882817, baseEnd_882817] using wordTrace_append hprefix tailTrace_882817
  have hstable : (prefixWord ++ tailWord_882817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882817).length < 2 ^ (prefixWord ++ tailWord_882817).sum := by decide
  have hdescent : baseEnd_882817 < baseStart_882817 := by decide
  rcases family_descends (prefixWord ++ tailWord_882817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882873 : List Nat := [1, 2, 1, 4, 1, 2, 3, 1, 2, 4, 2]
def baseStart_882873 : Nat := 118140960795 + 882873 * 2 ^ 59
def prefixEnd_882873 : Nat := 4983230072969 + 3 ^ 40 * 882873 * 2
def baseEnd_882873 : Nat := 453338205877029489027247

theorem tailTrace_882873 : CollatzResearch.WordTrace tailWord_882873 prefixEnd_882873 453338205877029489027247 := by
  unfold tailWord_882873
  simp only [CollatzResearch.WordTrace]
  refine ⟨32201023730509378549085273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21467349153672919032723515 32201023730509378549085273)
  ·
    refine ⟨24150767797882033911813955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32201023730509378549085273 24150767797882033911813955)
    ·
      refine ⟨36226151696823050867720933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24150767797882033911813955 36226151696823050867720933)
      ·
        refine ⟨6792403443154322037697675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36226151696823050867720933 6792403443154322037697675)
        ·
          refine ⟨10188605164731483056546513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6792403443154322037697675 10188605164731483056546513)
          ·
            refine ⟨7641453873548612292409885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10188605164731483056546513 7641453873548612292409885)
            ·
              refine ⟨2865545202580729609653707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7641453873548612292409885 2865545202580729609653707)
              ·
                refine ⟨4298317803871094414480561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2865545202580729609653707 4298317803871094414480561)
                ·
                  refine ⟨3223738352903320810860421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4298317803871094414480561 3223738352903320810860421)
                  ·
                    refine ⟨604450941169372652036329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3223738352903320810860421 604450941169372652036329)
                    ·
                      refine ⟨453338205877029489027247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 604450941169372652036329 453338205877029489027247)
                      ·
                        rfl

theorem cell23_882873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 2, 4, 2].length) (baseStart_882873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_882873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_882873 prefixEnd_882873 := by exact prefixLift 882873
  have htrace : WordTrace (prefixWord ++ tailWord_882873) baseStart_882873 baseEnd_882873 := by
    simpa [prefixWord, tailWord_882873, baseEnd_882873] using wordTrace_append hprefix tailTrace_882873
  have hstable : (prefixWord ++ tailWord_882873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882873).length < 2 ^ (prefixWord ++ tailWord_882873).sum := by decide
  have hdescent : baseEnd_882873 < baseStart_882873 := by decide
  rcases family_descends (prefixWord ++ tailWord_882873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882879 : List Nat := [1, 1, 2, 2, 2, 2, 1, 2, 10]
def baseStart_882879 : Nat := 118140960795 + 882879 * 2 ^ 59
def prefixEnd_882879 : Nat := 4983230072969 + 3 ^ 40 * 882879 * 2
def baseEnd_882879 : Nat := 50371254084550718394691

theorem tailTrace_882879 : CollatzResearch.WordTrace tailWord_882879 prefixEnd_882879 50371254084550718394691 := by
  unfold tailWord_882879
  simp only [CollatzResearch.WordTrace]
  refine ⟨32201242568487641573803691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21467495045658427715869127 32201242568487641573803691)
  ·
    refine ⟨48301863852731462360705537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32201242568487641573803691 48301863852731462360705537)
    ·
      refine ⟨36226397889548596770529153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48301863852731462360705537 36226397889548596770529153)
      ·
        refine ⟨27169798417161447577896865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36226397889548596770529153 27169798417161447577896865)
        ·
          refine ⟨20377348812871085683422649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27169798417161447577896865 20377348812871085683422649)
          ·
            refine ⟨15283011609653314262566987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20377348812871085683422649 15283011609653314262566987)
            ·
              refine ⟨22924517414479971393850481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15283011609653314262566987 22924517414479971393850481)
              ·
                refine ⟨17193388060859978545387861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22924517414479971393850481 17193388060859978545387861)
                ·
                  refine ⟨50371254084550718394691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 17193388060859978545387861 50371254084550718394691)
                  ·
                    rfl

theorem cell23_882879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 10].length) (baseStart_882879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_882879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_882879 prefixEnd_882879 := by exact prefixLift 882879
  have htrace : WordTrace (prefixWord ++ tailWord_882879) baseStart_882879 baseEnd_882879 := by
    simpa [prefixWord, tailWord_882879, baseEnd_882879] using wordTrace_append hprefix tailTrace_882879
  have hstable : (prefixWord ++ tailWord_882879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882879).length < 2 ^ (prefixWord ++ tailWord_882879).sum := by decide
  have hdescent : baseEnd_882879 < baseStart_882879 := by decide
  rcases family_descends (prefixWord ++ tailWord_882879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882899 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 8]
def baseStart_882899 : Nat := 118140960795 + 882899 * 2 ^ 59
def prefixEnd_882899 : Nat := 4983230072969 + 3 ^ 40 * 882899 * 2
def baseEnd_882899 : Nat := 453351556374046387302127

theorem tailTrace_882899 : CollatzResearch.WordTrace tailWord_882899 prefixEnd_882899 453351556374046387302127 := by
  unfold tailWord_882899
  simp only [CollatzResearch.WordTrace]
  refine ⟨32201972028415184989531751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21467981352276789993021167 32201972028415184989531751)
  ·
    refine ⟨48302958042622777484297627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32201972028415184989531751 48302958042622777484297627)
    ·
      refine ⟨72454437063934166226446441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48302958042622777484297627 72454437063934166226446441)
      ·
        refine ⟨54340827797950624669834831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72454437063934166226446441 54340827797950624669834831)
        ·
          refine ⟨81511241696925937004752247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54340827797950624669834831 81511241696925937004752247)
          ·
            refine ⟨122266862545388905507128371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81511241696925937004752247 122266862545388905507128371)
            ·
              refine ⟨183400293818083358260692557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122266862545388905507128371 183400293818083358260692557)
              ·
                refine ⟨68775110181781259347759709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 183400293818083358260692557 68775110181781259347759709)
                ·
                  refine ⟨25790666318167972255409891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68775110181781259347759709 25790666318167972255409891)
                  ·
                    refine ⟨38685999477251958383114837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25790666318167972255409891 38685999477251958383114837)
                    ·
                      refine ⟨453351556374046387302127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 38685999477251958383114837 453351556374046387302127)
                      ·
                        rfl

theorem cell23_882899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 8].length) (baseStart_882899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_882899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_882899 prefixEnd_882899 := by exact prefixLift 882899
  have htrace : WordTrace (prefixWord ++ tailWord_882899) baseStart_882899 baseEnd_882899 := by
    simpa [prefixWord, tailWord_882899, baseEnd_882899] using wordTrace_append hprefix tailTrace_882899
  have hstable : (prefixWord ++ tailWord_882899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882899).length < 2 ^ (prefixWord ++ tailWord_882899).sum := by decide
  have hdescent : baseEnd_882899 < baseStart_882899 := by decide
  rcases family_descends (prefixWord ++ tailWord_882899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882930 : List Nat := [3, 2, 1, 3, 2, 2, 3, 1, 6]
def baseStart_882930 : Nat := 118140960795 + 882930 * 2 ^ 59
def prefixEnd_882930 : Nat := 4983230072969 + 3 ^ 40 * 882930 * 2
def baseEnd_882930 : Nat := 50374163808259529557165

theorem tailTrace_882930 : CollatzResearch.WordTrace tailWord_882930 prefixEnd_882930 50374163808259529557165 := by
  unfold tailWord_882930
  simp only [CollatzResearch.WordTrace]
  refine ⟨8050775672825719320977561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21468735127535251522606829 8050775672825719320977561)
  ·
    refine ⟨6038081754619289490733171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8050775672825719320977561 6038081754619289490733171)
    ·
      refine ⟨9057122631928934236099757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6038081754619289490733171 9057122631928934236099757)
      ·
        refine ⟨3396420986973350338537409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9057122631928934236099757 3396420986973350338537409)
        ·
          refine ⟨2547315740230012753903057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3396420986973350338537409 2547315740230012753903057)
          ·
            refine ⟨1910486805172509565427293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2547315740230012753903057 1910486805172509565427293)
            ·
              refine ⟨716432551939691087035235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1910486805172509565427293 716432551939691087035235)
              ·
                refine ⟨1074648827909536630552853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 716432551939691087035235 1074648827909536630552853)
                ·
                  refine ⟨50374163808259529557165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1074648827909536630552853 50374163808259529557165)
                  ·
                    rfl

theorem cell23_882930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 3, 1, 6].length) (baseStart_882930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_882930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_882930 prefixEnd_882930 := by exact prefixLift 882930
  have htrace : WordTrace (prefixWord ++ tailWord_882930) baseStart_882930 baseEnd_882930 := by
    simpa [prefixWord, tailWord_882930, baseEnd_882930] using wordTrace_append hprefix tailTrace_882930
  have hstable : (prefixWord ++ tailWord_882930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882930).length < 2 ^ (prefixWord ++ tailWord_882930).sum := by decide
  have hdescent : baseEnd_882930 < baseStart_882930 := by decide
  rcases family_descends (prefixWord ++ tailWord_882930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882940 : List Nat := [2, 2, 2, 1, 4, 1, 2, 2, 3, 1, 3]
def baseStart_882940 : Nat := 118140960795 + 882940 * 2 ^ 59
def prefixEnd_882940 : Nat := 4983230072969 + 3 ^ 40 * 882940 * 2
def baseEnd_882940 : Nat := 453372609080880726889439

theorem tailTrace_882940 : CollatzResearch.WordTrace tailWord_882940 prefixEnd_882940 453372609080880726889439 := by
  unfold tailWord_882940
  simp only [CollatzResearch.WordTrace]
  refine ⟨16101733710633324495887137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21468978280844432661182849 16101733710633324495887137)
  ·
    refine ⟨12076300282974993371915353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16101733710633324495887137 12076300282974993371915353)
    ·
      refine ⟨9057225212231245028936515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12076300282974993371915353 9057225212231245028936515)
      ·
        refine ⟨13585837818346867543404773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9057225212231245028936515 13585837818346867543404773)
        ·
          refine ⟨2547344590940037664388395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13585837818346867543404773 2547344590940037664388395)
          ·
            refine ⟨3821016886410056496582593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2547344590940037664388395 3821016886410056496582593)
            ·
              refine ⟨2865762664807542372436945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3821016886410056496582593 2865762664807542372436945)
              ·
                refine ⟨2149321998605656779327709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2865762664807542372436945 2149321998605656779327709)
                ·
                  refine ⟨805995749477121292247891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2149321998605656779327709 805995749477121292247891)
                  ·
                    refine ⟨1208993624215681938371837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 805995749477121292247891 1208993624215681938371837)
                    ·
                      refine ⟨453372609080880726889439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1208993624215681938371837 453372609080880726889439)
                      ·
                        rfl

theorem cell23_882940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 2, 3, 1, 3].length) (baseStart_882940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_882940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_882940 prefixEnd_882940 := by exact prefixLift 882940
  have htrace : WordTrace (prefixWord ++ tailWord_882940) baseStart_882940 baseEnd_882940 := by
    simpa [prefixWord, tailWord_882940, baseEnd_882940] using wordTrace_append hprefix tailTrace_882940
  have hstable : (prefixWord ++ tailWord_882940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882940).length < 2 ^ (prefixWord ++ tailWord_882940).sum := by decide
  have hdescent : baseEnd_882940 < baseStart_882940 := by decide
  rcases family_descends (prefixWord ++ tailWord_882940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882943 : List Nat := [1, 1, 2, 2, 1, 4, 4, 2, 1, 5]
def baseStart_882943 : Nat := 118140960795 + 882943 * 2 ^ 59
def prefixEnd_882943 : Nat := 4983230072969 + 3 ^ 40 * 882943 * 2
def baseEnd_882943 : Nat := 151124716507614738383975

theorem tailTrace_882943 : CollatzResearch.WordTrace tailWord_882943 prefixEnd_882943 151124716507614738383975 := by
  unfold tailWord_882943
  simp only [CollatzResearch.WordTrace]
  refine ⟨32203576840255780504133483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21469051226837187002755655 32203576840255780504133483)
  ·
    refine ⟨48305365260383670756200225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32203576840255780504133483 48305365260383670756200225)
    ·
      refine ⟨36229023945287753067150169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48305365260383670756200225 36229023945287753067150169)
      ·
        refine ⟨27171767958965814800362627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36229023945287753067150169 27171767958965814800362627)
        ·
          refine ⟨40757651938448722200543941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27171767958965814800362627 40757651938448722200543941)
          ·
            refine ⟨7642059738459135412601989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40757651938448722200543941 7642059738459135412601989)
            ·
              refine ⟨1432886200961087889862873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7642059738459135412601989 1432886200961087889862873)
              ·
                refine ⟨1074664650720815917397155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1432886200961087889862873 1074664650720815917397155)
                ·
                  refine ⟨1611996976081223876095733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1074664650720815917397155 1611996976081223876095733)
                  ·
                    refine ⟨151124716507614738383975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1611996976081223876095733 151124716507614738383975)
                    ·
                      rfl

theorem cell23_882943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 2, 1, 5].length) (baseStart_882943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_882943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_882943 prefixEnd_882943 := by exact prefixLift 882943
  have htrace : WordTrace (prefixWord ++ tailWord_882943) baseStart_882943 baseEnd_882943 := by
    simpa [prefixWord, tailWord_882943, baseEnd_882943] using wordTrace_append hprefix tailTrace_882943
  have hstable : (prefixWord ++ tailWord_882943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882943).length < 2 ^ (prefixWord ++ tailWord_882943).sum := by decide
  have hdescent : baseEnd_882943 < baseStart_882943 := by decide
  rcases family_descends (prefixWord ++ tailWord_882943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882951 : List Nat := [1, 1, 4, 5, 2, 1, 1, 3, 1, 4]
def baseStart_882951 : Nat := 118140960795 + 882951 * 2 ^ 59
def prefixEnd_882951 : Nat := 4983230072969 + 3 ^ 40 * 882951 * 2
def baseEnd_882951 : Nat := 151126085789360061283963

theorem tailTrace_882951 : CollatzResearch.WordTrace tailWord_882951 prefixEnd_882951 151126085789360061283963 := by
  unfold tailWord_882951
  simp only [CollatzResearch.WordTrace]
  refine ⟨32203868624226797870424707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21469245749484531913616471 32203868624226797870424707)
  ·
    refine ⟨48305802936340196805637061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32203868624226797870424707 48305802936340196805637061)
    ·
      refine ⟨9057338050563786901056949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48305802936340196805637061 9057338050563786901056949)
      ·
        refine ⟨849125442240355021974089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9057338050563786901056949 849125442240355021974089)
        ·
          refine ⟨636844081680266266480567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 849125442240355021974089 636844081680266266480567)
          ·
            refine ⟨955266122520399399720851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 636844081680266266480567 955266122520399399720851)
            ·
              refine ⟨1432899183780599099581277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 955266122520399399720851 1432899183780599099581277)
              ·
                refine ⟨537337193917724662342979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1432899183780599099581277 537337193917724662342979)
                ·
                  refine ⟨806005790876586993514469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 537337193917724662342979 806005790876586993514469)
                  ·
                    refine ⟨151126085789360061283963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 806005790876586993514469 151126085789360061283963)
                    ·
                      rfl

theorem cell23_882951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 3, 1, 4].length) (baseStart_882951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_882951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_882951 prefixEnd_882951 := by exact prefixLift 882951
  have htrace : WordTrace (prefixWord ++ tailWord_882951) baseStart_882951 baseEnd_882951 := by
    simpa [prefixWord, tailWord_882951, baseEnd_882951] using wordTrace_append hprefix tailTrace_882951
  have hstable : (prefixWord ++ tailWord_882951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882951).length < 2 ^ (prefixWord ++ tailWord_882951).sum := by decide
  have hdescent : baseEnd_882951 < baseStart_882951 := by decide
  rcases family_descends (prefixWord ++ tailWord_882951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882956 : List Nat := [2, 2, 1, 2, 2, 2, 2, 1, 3, 6]
def baseStart_882956 : Nat := 118140960795 + 882956 * 2 ^ 59
def prefixEnd_882956 : Nat := 4983230072969 + 3 ^ 40 * 882956 * 2
def baseEnd_882956 : Nat := 151126941590450888096455

theorem tailTrace_882956 : CollatzResearch.WordTrace tailWord_882956 prefixEnd_882956 151126941590450888096455 := by
  unfold tailWord_882956
  simp only [CollatzResearch.WordTrace]
  refine ⟨16102025494604341862178361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21469367326139122482904481 16102025494604341862178361)
  ·
    refine ⟨12076519120953256396633771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16102025494604341862178361 12076519120953256396633771)
    ·
      refine ⟨18114778681429884594950657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12076519120953256396633771 18114778681429884594950657)
      ·
        refine ⟨13586084011072413446212993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18114778681429884594950657 13586084011072413446212993)
        ·
          refine ⟨10189563008304310084659745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13586084011072413446212993 10189563008304310084659745)
          ·
            refine ⟨7642172256228232563494809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10189563008304310084659745 7642172256228232563494809)
            ·
              refine ⟨5731629192171174422621107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7642172256228232563494809 5731629192171174422621107)
              ·
                refine ⟨8597443788256761633931661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5731629192171174422621107 8597443788256761633931661)
                ·
                  refine ⟨3224041420596285612724373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8597443788256761633931661 3224041420596285612724373)
                  ·
                    refine ⟨151126941590450888096455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3224041420596285612724373 151126941590450888096455)
                    ·
                      rfl

theorem cell23_882956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 3, 6].length) (baseStart_882956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_882956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_882956 prefixEnd_882956 := by exact prefixLift 882956
  have htrace : WordTrace (prefixWord ++ tailWord_882956) baseStart_882956 baseEnd_882956 := by
    simpa [prefixWord, tailWord_882956, baseEnd_882956] using wordTrace_append hprefix tailTrace_882956
  have hstable : (prefixWord ++ tailWord_882956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882956).length < 2 ^ (prefixWord ++ tailWord_882956).sum := by decide
  have hdescent : baseEnd_882956 < baseStart_882956 := by decide
  rcases family_descends (prefixWord ++ tailWord_882956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882974 : List Nat := [4, 3, 2, 1, 1, 1, 3, 1, 3, 1, 3]
def baseStart_882974 : Nat := 118140960795 + 882974 * 2 ^ 59
def prefixEnd_882974 : Nat := 4983230072969 + 3 ^ 40 * 882974 * 2
def baseEnd_882974 : Nat := 453390067423133593864283

theorem tailTrace_882974 : CollatzResearch.WordTrace tailWord_882974 prefixEnd_882974 453390067423133593864283 := by
  unfold tailWord_882974
  simp only [CollatzResearch.WordTrace]
  refine ⟨4025588437892934099813997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21469805002095648532341317 4025588437892934099813997)
  ·
    refine ⟨1509595664209850287430249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4025588437892934099813997 1509595664209850287430249)
    ·
      refine ⟨1132196748157387715572687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1509595664209850287430249 1132196748157387715572687)
      ·
        refine ⟨1698295122236081573359031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1132196748157387715572687 1698295122236081573359031)
        ·
          refine ⟨2547442683354122360038547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1698295122236081573359031 2547442683354122360038547)
          ·
            refine ⟨3821164025031183540057821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2547442683354122360038547 3821164025031183540057821)
            ·
              refine ⟨1432936509386693827521683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3821164025031183540057821 1432936509386693827521683)
              ·
                refine ⟨2149404764080040741282525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1432936509386693827521683 2149404764080040741282525)
                ·
                  refine ⟨806026786530015277980947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2149404764080040741282525 806026786530015277980947)
                  ·
                    refine ⟨1209040179795022916971421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 806026786530015277980947 1209040179795022916971421)
                    ·
                      refine ⟨453390067423133593864283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1209040179795022916971421 453390067423133593864283)
                      ·
                        rfl

theorem cell23_882974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_882974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_882974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_882974 prefixEnd_882974 := by exact prefixLift 882974
  have htrace : WordTrace (prefixWord ++ tailWord_882974) baseStart_882974 baseEnd_882974 := by
    simpa [prefixWord, tailWord_882974, baseEnd_882974] using wordTrace_append hprefix tailTrace_882974
  have hstable : (prefixWord ++ tailWord_882974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882974).length < 2 ^ (prefixWord ++ tailWord_882974).sum := by decide
  have hdescent : baseEnd_882974 < baseStart_882974 := by decide
  rcases family_descends (prefixWord ++ tailWord_882974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883000 : List Nat := [2, 1, 2, 1, 3, 1, 5, 2, 1, 2, 3]
def baseStart_883000 : Nat := 118140960795 + 883000 * 2 ^ 59
def prefixEnd_883000 : Nat := 4983230072969 + 3 ^ 40 * 883000 * 2
def baseEnd_883000 : Nat := 453403417920150492139163

theorem tailTrace_883000 : CollatzResearch.WordTrace tailWord_883000 prefixEnd_883000 453403417920150492139163 := by
  unfold tailWord_883000
  simp only [CollatzResearch.WordTrace]
  refine ⟨16102827900524639619479227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21470437200699519492638969 16102827900524639619479227)
  ·
    refine ⟨24154241850786959429218841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16102827900524639619479227 24154241850786959429218841)
    ·
      refine ⟨18115681388090219571914131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24154241850786959429218841 18115681388090219571914131)
      ·
        refine ⟨27173522082135329357871197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18115681388090219571914131 27173522082135329357871197)
        ·
          refine ⟨10190070780800748509201699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27173522082135329357871197 10190070780800748509201699)
          ·
            refine ⟨15285106171201122763802549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10190070780800748509201699 15285106171201122763802549)
            ·
              refine ⟨1432978703550105259106489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15285106171201122763802549 1432978703550105259106489)
              ·
                refine ⟨1074734027662578944329867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1432978703550105259106489 1074734027662578944329867)
                ·
                  refine ⟨1612101041493868416494801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1074734027662578944329867 1612101041493868416494801)
                  ·
                    refine ⟨1209075781120401312371101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1612101041493868416494801 1209075781120401312371101)
                    ·
                      refine ⟨453403417920150492139163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1209075781120401312371101 453403417920150492139163)
                      ·
                        rfl

theorem cell23_883000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 2, 1, 2, 3].length) (baseStart_883000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_883000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_883000 prefixEnd_883000 := by exact prefixLift 883000
  have htrace : WordTrace (prefixWord ++ tailWord_883000) baseStart_883000 baseEnd_883000 := by
    simpa [prefixWord, tailWord_883000, baseEnd_883000] using wordTrace_append hprefix tailTrace_883000
  have hstable : (prefixWord ++ tailWord_883000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883000).length < 2 ^ (prefixWord ++ tailWord_883000).sum := by decide
  have hdescent : baseEnd_883000 < baseStart_883000 := by decide
  rcases family_descends (prefixWord ++ tailWord_883000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883047 : List Nat := [1, 1, 5, 1, 3, 1, 2, 3, 2, 1, 3]
def baseStart_883047 : Nat := 118140960795 + 883047 * 2 ^ 59
def prefixEnd_883047 : Nat := 4983230072969 + 3 ^ 40 * 883047 * 2
def baseEnd_883047 : Nat := 453427551510911808251447

theorem tailTrace_883047 : CollatzResearch.WordTrace tailWord_883047 prefixEnd_883047 453427551510911808251447 := by
  unfold tailWord_883047
  simp only [CollatzResearch.WordTrace]
  refine ⟨32207370031879006265919395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21471580021252670843946263 32207370031879006265919395)
  ·
    refine ⟨48311055047818509398879093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32207370031879006265919395 48311055047818509398879093)
    ·
      refine ⟨4529161410732985256144915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48311055047818509398879093 4529161410732985256144915)
      ·
        refine ⟨6793742116099477884217373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4529161410732985256144915 6793742116099477884217373)
        ·
          refine ⟨2547653293537304206581515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6793742116099477884217373 2547653293537304206581515)
          ·
            refine ⟨3821479940305956309872273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2547653293537304206581515 3821479940305956309872273)
            ·
              refine ⟨2866109955229467232404205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3821479940305956309872273 2866109955229467232404205)
              ·
                refine ⟨1074791233211050212151577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2866109955229467232404205 1074791233211050212151577)
                ·
                  refine ⟨806093424908287659113683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1074791233211050212151577 806093424908287659113683)
                  ·
                    refine ⟨1209140137362431488670525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 806093424908287659113683 1209140137362431488670525)
                    ·
                      refine ⟨453427551510911808251447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1209140137362431488670525 453427551510911808251447)
                      ·
                        rfl

theorem cell23_883047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 3, 2, 1, 3].length) (baseStart_883047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_883047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_883047 prefixEnd_883047 := by exact prefixLift 883047
  have htrace : WordTrace (prefixWord ++ tailWord_883047) baseStart_883047 baseEnd_883047 := by
    simpa [prefixWord, tailWord_883047, baseEnd_883047] using wordTrace_append hprefix tailTrace_883047
  have hstable : (prefixWord ++ tailWord_883047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883047).length < 2 ^ (prefixWord ++ tailWord_883047).sum := by decide
  have hdescent : baseEnd_883047 < baseStart_883047 := by decide
  rcases family_descends (prefixWord ++ tailWord_883047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883053 : List Nat := [1, 5, 1, 1, 1, 2, 1, 2, 2, 3, 4]
def baseStart_883053 : Nat := 118140960795 + 883053 * 2 ^ 59
def prefixEnd_883053 : Nat := 4983230072969 + 3 ^ 40 * 883053 * 2
def baseEnd_883053 : Nat := 453430632394838784776419

theorem tailTrace_883053 : CollatzResearch.WordTrace tailWord_883053 prefixEnd_883053 453430632394838784776419 := by
  unfold tailWord_883053
  simp only [CollatzResearch.WordTrace]
  refine ⟨32207588869857269290637813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21471725913238179527091875 32207588869857269290637813)
  ·
    refine ⟨3019461456549118995997295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32207588869857269290637813 3019461456549118995997295)
    ·
      refine ⟨4529192184823678493995943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3019461456549118995997295 4529192184823678493995943)
      ·
        refine ⟨6793788277235517740993915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4529192184823678493995943 6793788277235517740993915)
        ·
          refine ⟨10190682415853276611490873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6793788277235517740993915 10190682415853276611490873)
          ·
            refine ⟨7643011811889957458618155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10190682415853276611490873 7643011811889957458618155)
            ·
              refine ⟨11464517717834936187927233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7643011811889957458618155 11464517717834936187927233)
              ·
                refine ⟨8598388288376202140945425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11464517717834936187927233 8598388288376202140945425)
                ·
                  refine ⟨6448791216282151605709069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8598388288376202140945425 6448791216282151605709069)
                  ·
                    refine ⟨2418296706105806852140901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6448791216282151605709069 2418296706105806852140901)
                    ·
                      refine ⟨453430632394838784776419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2418296706105806852140901 453430632394838784776419)
                      ·
                        rfl

theorem cell23_883053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_883053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_883053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_883053 prefixEnd_883053 := by exact prefixLift 883053
  have htrace : WordTrace (prefixWord ++ tailWord_883053) baseStart_883053 baseEnd_883053 := by
    simpa [prefixWord, tailWord_883053, baseEnd_883053] using wordTrace_append hprefix tailTrace_883053
  have hstable : (prefixWord ++ tailWord_883053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883053).length < 2 ^ (prefixWord ++ tailWord_883053).sum := by decide
  have hdescent : baseEnd_883053 < baseStart_883053 := by decide
  rcases family_descends (prefixWord ++ tailWord_883053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883083 : List Nat := [1, 1, 1, 1, 4, 4, 1, 2, 2, 2, 4]
def baseStart_883083 : Nat := 118140960795 + 883083 * 2 ^ 59
def prefixEnd_883083 : Nat := 4983230072969 + 3 ^ 40 * 883083 * 2
def baseEnd_883083 : Nat := 453446036814473667401281

theorem tailTrace_883083 : CollatzResearch.WordTrace tailWord_883083 prefixEnd_883083 453446036814473667401281 := by
  unfold tailWord_883083
  simp only [CollatzResearch.WordTrace]
  refine ⟨32208683059748584414229903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21472455373165722942819935 32208683059748584414229903)
  ·
    refine ⟨48313024589622876621344855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32208683059748584414229903 48313024589622876621344855)
    ·
      refine ⟨72469536884434314932017283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48313024589622876621344855 72469536884434314932017283)
      ·
        refine ⟨108704305326651472398025925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72469536884434314932017283 108704305326651472398025925)
        ·
          refine ⟨20382057248747151074629861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108704305326651472398025925 20382057248747151074629861)
          ·
            refine ⟨3821635734140090826493099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20382057248747151074629861 3821635734140090826493099)
            ·
              refine ⟨5732453601210136239739649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3821635734140090826493099 5732453601210136239739649)
              ·
                refine ⟨4299340200907602179804737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5732453601210136239739649 4299340200907602179804737)
                ·
                  refine ⟨3224505150680701634853553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4299340200907602179804737 3224505150680701634853553)
                  ·
                    refine ⟨2418378863010526226140165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3224505150680701634853553 2418378863010526226140165)
                    ·
                      refine ⟨453446036814473667401281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2418378863010526226140165 453446036814473667401281)
                      ·
                        rfl

theorem cell23_883083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 2, 2, 4].length) (baseStart_883083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_883083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_883083 prefixEnd_883083 := by exact prefixLift 883083
  have htrace : WordTrace (prefixWord ++ tailWord_883083) baseStart_883083 baseEnd_883083 := by
    simpa [prefixWord, tailWord_883083, baseEnd_883083] using wordTrace_append hprefix tailTrace_883083
  have hstable : (prefixWord ++ tailWord_883083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883083).length < 2 ^ (prefixWord ++ tailWord_883083).sum := by decide
  have hdescent : baseEnd_883083 < baseStart_883083 := by decide
  rcases family_descends (prefixWord ++ tailWord_883083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883124 : List Nat := [2, 5, 2, 2, 1, 1, 1, 1, 2, 1, 5]
def baseStart_883124 : Nat := 118140960795 + 883124 * 2 ^ 59
def prefixEnd_883124 : Nat := 4983230072969 + 3 ^ 40 * 883124 * 2
def baseEnd_883124 : Nat := 453467089521308006988593

theorem tailTrace_883124 : CollatzResearch.WordTrace tailWord_883124 prefixEnd_883124 453467089521308006988593 := by
  unfold tailWord_883124
  simp only [CollatzResearch.WordTrace]
  refine ⟨16105089226300024208236213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21473452301733365610981617 16105089226300024208236213)
  ·
    refine ⟨1509852114965627269522145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16105089226300024208236213 1509852114965627269522145)
    ·
      refine ⟨1132389086224220452141609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1509852114965627269522145 1132389086224220452141609)
      ·
        refine ⟨849291814668165339106207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1132389086224220452141609 849291814668165339106207)
        ·
          refine ⟨1273937722002248008659311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 849291814668165339106207 1273937722002248008659311)
          ·
            refine ⟨1910906583003372012988967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1273937722002248008659311 1910906583003372012988967)
            ·
              refine ⟨2866359874505058019483451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1910906583003372012988967 2866359874505058019483451)
              ·
                refine ⟨4299539811757587029225177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2866359874505058019483451 4299539811757587029225177)
                ·
                  refine ⟨3224654858818190271918883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4299539811757587029225177 3224654858818190271918883)
                  ·
                    refine ⟨4836982288227285407878325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3224654858818190271918883 4836982288227285407878325)
                    ·
                      refine ⟨453467089521308006988593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4836982288227285407878325 453467089521308006988593)
                      ·
                        rfl

theorem cell23_883124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_883124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_883124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_883124 prefixEnd_883124 := by exact prefixLift 883124
  have htrace : WordTrace (prefixWord ++ tailWord_883124) baseStart_883124 baseEnd_883124 := by
    simpa [prefixWord, tailWord_883124, baseEnd_883124] using wordTrace_append hprefix tailTrace_883124
  have hstable : (prefixWord ++ tailWord_883124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883124).length < 2 ^ (prefixWord ++ tailWord_883124).sum := by decide
  have hdescent : baseEnd_883124 < baseStart_883124 := by decide
  rcases family_descends (prefixWord ++ tailWord_883124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883127 : List Nat := [1, 1, 3, 1, 3, 5, 1, 3, 5]
def baseStart_883127 : Nat := 118140960795 + 883127 * 2 ^ 59
def prefixEnd_883127 : Nat := 4983230072969 + 3 ^ 40 * 883127 * 2
def baseEnd_883127 : Nat := 50385403329252388361231

theorem tailTrace_883127 : CollatzResearch.WordTrace tailWord_883127 prefixEnd_883127 50385403329252388361231 := by
  unfold tailWord_883127
  simp only [CollatzResearch.WordTrace]
  refine ⟨32210287871589179928831635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21473525247726119952554423 32210287871589179928831635)
  ·
    refine ⟨48315431807383769893247453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32210287871589179928831635 48315431807383769893247453)
    ·
      refine ⟨18118286927768913709967795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48315431807383769893247453 18118286927768913709967795)
      ·
        refine ⟨27177430391653370564951693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18118286927768913709967795 27177430391653370564951693)
        ·
          refine ⟨10191536396870013961856885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27177430391653370564951693 10191536396870013961856885)
          ·
            refine ⟨955456537206563808924083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10191536396870013961856885 955456537206563808924083)
            ·
              refine ⟨1433184805809845713386125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 955456537206563808924083 1433184805809845713386125)
              ·
                refine ⟨537444302178692142519797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1433184805809845713386125 537444302178692142519797)
                ·
                  refine ⟨50385403329252388361231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 537444302178692142519797 50385403329252388361231)
                  ·
                    rfl

theorem cell23_883127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 3, 5].length) (baseStart_883127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_883127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_883127 prefixEnd_883127 := by exact prefixLift 883127
  have htrace : WordTrace (prefixWord ++ tailWord_883127) baseStart_883127 baseEnd_883127 := by
    simpa [prefixWord, tailWord_883127, baseEnd_883127] using wordTrace_append hprefix tailTrace_883127
  have hstable : (prefixWord ++ tailWord_883127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883127).length < 2 ^ (prefixWord ++ tailWord_883127).sum := by decide
  have hdescent : baseEnd_883127 < baseStart_883127 := by decide
  rcases family_descends (prefixWord ++ tailWord_883127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883160 : List Nat := [2, 1, 2, 2, 2, 1, 1, 3, 1, 6, 2]
def baseStart_883160 : Nat := 118140960795 + 883160 * 2 ^ 59
def prefixEnd_883160 : Nat := 4983230072969 + 3 ^ 40 * 883160 * 2
def baseEnd_883160 : Nat := 453485574824869866138427

theorem tailTrace_883160 : CollatzResearch.WordTrace tailWord_883160 prefixEnd_883160 453485574824869866138427 := by
  unfold tailWord_883160
  simp only [CollatzResearch.WordTrace]
  refine ⟨16105745740234813282391467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21474327653646417709855289 16105745740234813282391467)
  ·
    refine ⟨24158618610352219923587201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16105745740234813282391467 24158618610352219923587201)
    ·
      refine ⟨18118963957764164942690401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24158618610352219923587201 18118963957764164942690401)
      ·
        refine ⟨13589222968323123707017801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18118963957764164942690401 13589222968323123707017801)
        ·
          refine ⟨10191917226242342780263351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13589222968323123707017801 10191917226242342780263351)
          ·
            refine ⟨15287875839363514170395027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10191917226242342780263351 15287875839363514170395027)
            ·
              refine ⟨22931813759045271255592541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15287875839363514170395027 22931813759045271255592541)
              ·
                refine ⟨8599430159641976720847203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22931813759045271255592541 8599430159641976720847203)
                ·
                  refine ⟨12899145239462965081270805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8599430159641976720847203 12899145239462965081270805)
                  ·
                    refine ⟨604647433099826488184569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12899145239462965081270805 604647433099826488184569)
                    ·
                      refine ⟨453485574824869866138427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 604647433099826488184569 453485574824869866138427)
                      ·
                        rfl

theorem cell23_883160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 1, 6, 2].length) (baseStart_883160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_883160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_883160 prefixEnd_883160 := by exact prefixLift 883160
  have htrace : WordTrace (prefixWord ++ tailWord_883160) baseStart_883160 baseEnd_883160 := by
    simpa [prefixWord, tailWord_883160, baseEnd_883160] using wordTrace_append hprefix tailTrace_883160
  have hstable : (prefixWord ++ tailWord_883160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883160).length < 2 ^ (prefixWord ++ tailWord_883160).sum := by decide
  have hdescent : baseEnd_883160 < baseStart_883160 := by decide
  rcases family_descends (prefixWord ++ tailWord_883160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883187 : List Nat := [1, 1, 1, 2, 2, 2, 4, 5, 1, 4]
def baseStart_883187 : Nat := 118140960795 + 883187 * 2 ^ 59
def prefixEnd_883187 : Nat := 4983230072969 + 3 ^ 40 * 883187 * 2
def baseEnd_883187 : Nat := 151166479600847086833601

theorem tailTrace_883187 : CollatzResearch.WordTrace tailWord_883187 prefixEnd_883187 151166479600847086833601 := by
  unfold tailWord_883187
  simp only [CollatzResearch.WordTrace]
  refine ⟨32212476251371810176015815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21474984167581206784010543 32212476251371810176015815)
  ·
    refine ⟨48318714377057715264023723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32212476251371810176015815 48318714377057715264023723)
    ·
      refine ⟨72478071565586572896035585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48318714377057715264023723 72478071565586572896035585)
      ·
        refine ⟨54358553674189929672026689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72478071565586572896035585 54358553674189929672026689)
        ·
          refine ⟨40768915255642447254020017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54358553674189929672026689 40768915255642447254020017)
          ·
            refine ⟨30576686441731835440515013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40768915255642447254020017 30576686441731835440515013)
            ·
              refine ⟨5733128707824719145096565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30576686441731835440515013 5733128707824719145096565)
              ·
                refine ⟨537480816358567419852803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5733128707824719145096565 537480816358567419852803)
                ·
                  refine ⟨806221224537851129779205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 537480816358567419852803 806221224537851129779205)
                  ·
                    refine ⟨151166479600847086833601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 806221224537851129779205 151166479600847086833601)
                    ·
                      rfl

theorem cell23_883187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 5, 1, 4].length) (baseStart_883187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_883187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_883187 prefixEnd_883187 := by exact prefixLift 883187
  have htrace : WordTrace (prefixWord ++ tailWord_883187) baseStart_883187 baseEnd_883187 := by
    simpa [prefixWord, tailWord_883187, baseEnd_883187] using wordTrace_append hprefix tailTrace_883187
  have hstable : (prefixWord ++ tailWord_883187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883187).length < 2 ^ (prefixWord ++ tailWord_883187).sum := by decide
  have hdescent : baseEnd_883187 < baseStart_883187 := by decide
  rcases family_descends (prefixWord ++ tailWord_883187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883190 : List Nat := [5, 1, 1, 1, 2, 1, 2, 1, 2, 1, 6]
def baseStart_883190 : Nat := 118140960795 + 883190 * 2 ^ 59
def prefixEnd_883190 : Nat := 4983230072969 + 3 ^ 40 * 883190 * 2
def baseEnd_883190 : Nat := 453500979244504748763289

theorem tailTrace_883190 : CollatzResearch.WordTrace tailWord_883190 prefixEnd_883190 453500979244504748763289 := by
  unfold tailWord_883190
  simp only [CollatzResearch.WordTrace]
  refine ⟨2013286604397558855523439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21475057113573961125583349 2013286604397558855523439)
  ·
    refine ⟨3019929906596338283285159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2013286604397558855523439 3019929906596338283285159)
    ·
      refine ⟨4529894859894507424927739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3019929906596338283285159 4529894859894507424927739)
      ·
        refine ⟨6794842289841761137391609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4529894859894507424927739 6794842289841761137391609)
        ·
          refine ⟨5096131717381320853043707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6794842289841761137391609 5096131717381320853043707)
          ·
            refine ⟨7644197576071981279565561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5096131717381320853043707 7644197576071981279565561)
            ·
              refine ⟨5733148182053985959674171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7644197576071981279565561 5733148182053985959674171)
              ·
                refine ⟨8599722273080978939511257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5733148182053985959674171 8599722273080978939511257)
                ·
                  refine ⟨6449791704810734204633443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8599722273080978939511257 6449791704810734204633443)
                  ·
                    refine ⟨9674687557216101306950165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6449791704810734204633443 9674687557216101306950165)
                    ·
                      refine ⟨453500979244504748763289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9674687557216101306950165 453500979244504748763289)
                      ·
                        rfl

theorem cell23_883190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_883190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_883190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_883190 prefixEnd_883190 := by exact prefixLift 883190
  have htrace : WordTrace (prefixWord ++ tailWord_883190) baseStart_883190 baseEnd_883190 := by
    simpa [prefixWord, tailWord_883190, baseEnd_883190] using wordTrace_append hprefix tailTrace_883190
  have hstable : (prefixWord ++ tailWord_883190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883190).length < 2 ^ (prefixWord ++ tailWord_883190).sum := by decide
  have hdescent : baseEnd_883190 < baseStart_883190 := by decide
  rcases family_descends (prefixWord ++ tailWord_883190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883203 : List Nat := [1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 6]
def baseStart_883203 : Nat := 118140960795 + 883203 * 2 ^ 59
def prefixEnd_883203 : Nat := 4983230072969 + 3 ^ 40 * 883203 * 2
def baseEnd_883203 : Nat := 453507654493013197900729

theorem tailTrace_883203 : CollatzResearch.WordTrace tailWord_883203 prefixEnd_883203 453507654493013197900729 := by
  unfold tailWord_883203
  simp only [CollatzResearch.WordTrace]
  refine ⟨32213059819313844908598263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21475373212875896605732175 32213059819313844908598263)
  ·
    refine ⟨48319589728970767362897395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32213059819313844908598263 48319589728970767362897395)
    ·
      refine ⟨72479384593456151044346093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48319589728970767362897395 72479384593456151044346093)
      ·
        refine ⟨27179769222546056641629785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72479384593456151044346093 27179769222546056641629785)
        ·
          refine ⟨20384826916909542481222339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27179769222546056641629785 20384826916909542481222339)
          ·
            refine ⟨30577240375364313721833509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20384826916909542481222339 30577240375364313721833509)
            ·
              refine ⟨5733232570380808822843783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30577240375364313721833509 5733232570380808822843783)
              ·
                refine ⟨8599848855571213234265675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5733232570380808822843783 8599848855571213234265675)
                ·
                  refine ⟨12899773283356819851398513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8599848855571213234265675 12899773283356819851398513)
                  ·
                    refine ⟨9674829962517614888548885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12899773283356819851398513 9674829962517614888548885)
                    ·
                      refine ⟨453507654493013197900729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9674829962517614888548885 453507654493013197900729)
                      ·
                        rfl

theorem cell23_883203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 6].length) (baseStart_883203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_883203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_883203 prefixEnd_883203 := by exact prefixLift 883203
  have htrace : WordTrace (prefixWord ++ tailWord_883203) baseStart_883203 baseEnd_883203 := by
    simpa [prefixWord, tailWord_883203, baseEnd_883203] using wordTrace_append hprefix tailTrace_883203
  have hstable : (prefixWord ++ tailWord_883203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883203).length < 2 ^ (prefixWord ++ tailWord_883203).sum := by decide
  have hdescent : baseEnd_883203 < baseStart_883203 := by decide
  rcases family_descends (prefixWord ++ tailWord_883203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883261 : List Nat := [1, 4, 1, 3, 2, 1, 2, 4, 1, 1, 3]
def baseStart_883261 : Nat := 118140960795 + 883261 * 2 ^ 59
def prefixEnd_883261 : Nat := 4983230072969 + 3 ^ 40 * 883261 * 2
def baseEnd_883261 : Nat := 453537436370973970975463

theorem tailTrace_883261 : CollatzResearch.WordTrace tailWord_883261 prefixEnd_883261 453537436370973970975463 := by
  unfold tailWord_883261
  simp only [CollatzResearch.WordTrace]
  refine ⟨32215175253103720814209637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21476783502069147209473091 32215175253103720814209637)
  ·
    refine ⟨6040345359956947652664307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32215175253103720814209637 6040345359956947652664307)
    ·
      refine ⟨9060518039935421478996461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6040345359956947652664307 9060518039935421478996461)
      ·
        refine ⟨3397694264975783054623673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9060518039935421478996461 3397694264975783054623673)
        ·
          refine ⟨2548270698731837290967755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3397694264975783054623673 2548270698731837290967755)
          ·
            refine ⟨3822406048097755936451633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2548270698731837290967755 3822406048097755936451633)
            ·
              refine ⟨2866804536073316952338725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3822406048097755936451633 2866804536073316952338725)
              ·
                refine ⟨537525850513746928563511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2866804536073316952338725 537525850513746928563511)
                ·
                  refine ⟨806288775770620392845267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 537525850513746928563511 806288775770620392845267)
                  ·
                    refine ⟨1209433163655930589267901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 806288775770620392845267 1209433163655930589267901)
                    ·
                      refine ⟨453537436370973970975463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1209433163655930589267901 453537436370973970975463)
                      ·
                        rfl

theorem cell23_883261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 4, 1, 1, 3].length) (baseStart_883261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_883261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_883261 prefixEnd_883261 := by exact prefixLift 883261
  have htrace : WordTrace (prefixWord ++ tailWord_883261) baseStart_883261 baseEnd_883261 := by
    simpa [prefixWord, tailWord_883261, baseEnd_883261] using wordTrace_append hprefix tailTrace_883261
  have hstable : (prefixWord ++ tailWord_883261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883261).length < 2 ^ (prefixWord ++ tailWord_883261).sum := by decide
  have hdescent : baseEnd_883261 < baseStart_883261 := by decide
  rcases family_descends (prefixWord ++ tailWord_883261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883268 : List Nat := [2, 3, 5, 1, 1, 1, 3, 1, 6]
def baseStart_883268 : Nat := 118140960795 + 883268 * 2 ^ 59
def prefixEnd_883268 : Nat := 4983230072969 + 3 ^ 40 * 883268 * 2
def baseEnd_883268 : Nat := 50393447859506160398659

theorem tailTrace_883268 : CollatzResearch.WordTrace tailWord_883268 prefixEnd_883268 50393447859506160398659 := by
  unfold tailWord_883268
  simp only [CollatzResearch.WordTrace]
  refine ⟨16107715282039180504857229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21476953709385574006476305 16107715282039180504857229)
  ·
    refine ⟨6040393230764692689321461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16107715282039180504857229 6040393230764692689321461)
    ·
      refine ⟨566286865384189939623887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6040393230764692689321461 566286865384189939623887)
      ·
        refine ⟨849430298076284909435831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 566286865384189939623887 849430298076284909435831)
        ·
          refine ⟨1274145447114427364153747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 849430298076284909435831 1274145447114427364153747)
          ·
            refine ⟨1911218170671641046230621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1274145447114427364153747 1911218170671641046230621)
            ·
              refine ⟨716706814001865392336483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1911218170671641046230621 716706814001865392336483)
              ·
                refine ⟨1075060221002798088504725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 716706814001865392336483 1075060221002798088504725)
                ·
                  refine ⟨50393447859506160398659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1075060221002798088504725 50393447859506160398659)
                  ·
                    rfl

theorem cell23_883268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 3, 1, 6].length) (baseStart_883268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_883268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_883268 prefixEnd_883268 := by exact prefixLift 883268
  have htrace : WordTrace (prefixWord ++ tailWord_883268) baseStart_883268 baseEnd_883268 := by
    simpa [prefixWord, tailWord_883268, baseEnd_883268] using wordTrace_append hprefix tailTrace_883268
  have hstable : (prefixWord ++ tailWord_883268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883268).length < 2 ^ (prefixWord ++ tailWord_883268).sum := by decide
  have hdescent : baseEnd_883268 < baseStart_883268 := by decide
  rcases family_descends (prefixWord ++ tailWord_883268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883280 : List Nat := [2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 4]
def baseStart_883280 : Nat := 118140960795 + 883280 * 2 ^ 59
def prefixEnd_883280 : Nat := 4983230072969 + 3 ^ 40 * 883280 * 2
def baseEnd_883280 : Nat := 453547192503409396637875

theorem tailTrace_883280 : CollatzResearch.WordTrace tailWord_883280 prefixEnd_883280 453547192503409396637875 := by
  unfold tailWord_883280
  simp only [CollatzResearch.WordTrace]
  refine ⟨16107934120017443529575647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21477245493356591372767529 16107934120017443529575647)
  ·
    refine ⟨24161901180026165294363471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16107934120017443529575647 24161901180026165294363471)
    ·
      refine ⟨36242851770039247941545207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24161901180026165294363471 36242851770039247941545207)
      ·
        refine ⟨54364277655058871912317811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36242851770039247941545207 54364277655058871912317811)
        ·
          refine ⟨81546416482588307868476717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54364277655058871912317811 81546416482588307868476717)
          ·
            refine ⟨30579906180970615450678769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81546416482588307868476717 30579906180970615450678769)
            ·
              refine ⟨22934929635727961588009077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30579906180970615450678769 22934929635727961588009077)
              ·
                refine ⟨2150149653349496398875851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22934929635727961588009077 2150149653349496398875851)
                ·
                  refine ⟨3225224480024244598313777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2150149653349496398875851 3225224480024244598313777)
                  ·
                    refine ⟨2418918360018183448735333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3225224480024244598313777 2418918360018183448735333)
                    ·
                      refine ⟨453547192503409396637875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2418918360018183448735333 453547192503409396637875)
                      ·
                        rfl

theorem cell23_883280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 4].length) (baseStart_883280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_883280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_883280 prefixEnd_883280 := by exact prefixLift 883280
  have htrace : WordTrace (prefixWord ++ tailWord_883280) baseStart_883280 baseEnd_883280 := by
    simpa [prefixWord, tailWord_883280, baseEnd_883280] using wordTrace_append hprefix tailTrace_883280
  have hstable : (prefixWord ++ tailWord_883280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883280).length < 2 ^ (prefixWord ++ tailWord_883280).sum := by decide
  have hdescent : baseEnd_883280 < baseStart_883280 := by decide
  rcases family_descends (prefixWord ++ tailWord_883280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883284 : List Nat := [2, 4, 1, 1, 1, 4, 2, 2, 1, 1, 4]
def baseStart_883284 : Nat := 118140960795 + 883284 * 2 ^ 59
def prefixEnd_883284 : Nat := 4983230072969 + 3 ^ 40 * 883284 * 2
def baseEnd_883284 : Nat := 453549246426027380987857

theorem tailTrace_883284 : CollatzResearch.WordTrace tailWord_883284 prefixEnd_883284 453549246426027380987857 := by
  unfold tailWord_883284
  simp only [CollatzResearch.WordTrace]
  refine ⟨16108007066010197871148453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21477342754680263828197937 16108007066010197871148453)
  ·
    refine ⟨3020251324876912100840335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16108007066010197871148453 3020251324876912100840335)
    ·
      refine ⟨4530376987315368151260503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3020251324876912100840335 4530376987315368151260503)
      ·
        refine ⟨6795565480973052226890755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4530376987315368151260503 6795565480973052226890755)
        ·
          refine ⟨10193348221459578340336133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6795565480973052226890755 10193348221459578340336133)
          ·
            refine ⟨1911252791523670938813025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10193348221459578340336133 1911252791523670938813025)
            ·
              refine ⟨1433439593642753204109769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1911252791523670938813025 1433439593642753204109769)
              ·
                refine ⟨1075079695232064903082327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1433439593642753204109769 1075079695232064903082327)
                ·
                  refine ⟨1612619542848097354623491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1075079695232064903082327 1612619542848097354623491)
                  ·
                    refine ⟨2418929314272146031935237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1612619542848097354623491 2418929314272146031935237)
                    ·
                      refine ⟨453549246426027380987857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2418929314272146031935237 453549246426027380987857)
                      ·
                        rfl

theorem cell23_883284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 2, 1, 1, 4].length) (baseStart_883284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_883284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_883284 prefixEnd_883284 := by exact prefixLift 883284
  have htrace : WordTrace (prefixWord ++ tailWord_883284) baseStart_883284 baseEnd_883284 := by
    simpa [prefixWord, tailWord_883284, baseEnd_883284] using wordTrace_append hprefix tailTrace_883284
  have hstable : (prefixWord ++ tailWord_883284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883284).length < 2 ^ (prefixWord ++ tailWord_883284).sum := by decide
  have hdescent : baseEnd_883284 < baseStart_883284 := by decide
  rcases family_descends (prefixWord ++ tailWord_883284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883304 : List Nat := [2, 1, 4, 3, 2, 1, 2, 1, 1, 1, 5]
def baseStart_883304 : Nat := 118140960795 + 883304 * 2 ^ 59
def prefixEnd_883304 : Nat := 4983230072969 + 3 ^ 40 * 883304 * 2
def baseEnd_883304 : Nat := 453559516039117302737765

theorem tailTrace_883304 : CollatzResearch.WordTrace tailWord_883304 prefixEnd_883304 453559516039117302737765 := by
  unfold tailWord_883304
  simp only [CollatzResearch.WordTrace]
  refine ⟨16108371795973969579012483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21477829061298626105349977 16108371795973969579012483)
  ·
    refine ⟨24162557693960954368518725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16108371795973969579012483 24162557693960954368518725)
    ·
      refine ⟨4530479567617678944097261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24162557693960954368518725 4530479567617678944097261)
      ·
        refine ⟨1698929837856629604036473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4530479567617678944097261 1698929837856629604036473)
        ·
          refine ⟨1274197378392472203027355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1698929837856629604036473 1274197378392472203027355)
          ·
            refine ⟨1911296067588708304541033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1274197378392472203027355 1911296067588708304541033)
            ·
              refine ⟨1433472050691531228405775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1911296067588708304541033 1433472050691531228405775)
              ·
                refine ⟨2150208076037296842608663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1433472050691531228405775 2150208076037296842608663)
                ·
                  refine ⟨3225312114055945263912995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2150208076037296842608663 3225312114055945263912995)
                  ·
                    refine ⟨4837968171083917895869493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3225312114055945263912995 4837968171083917895869493)
                    ·
                      refine ⟨453559516039117302737765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4837968171083917895869493 453559516039117302737765)
                      ·
                        rfl

theorem cell23_883304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_883304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_883304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_883304 prefixEnd_883304 := by exact prefixLift 883304
  have htrace : WordTrace (prefixWord ++ tailWord_883304) baseStart_883304 baseEnd_883304 := by
    simpa [prefixWord, tailWord_883304, baseEnd_883304] using wordTrace_append hprefix tailTrace_883304
  have hstable : (prefixWord ++ tailWord_883304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883304).length < 2 ^ (prefixWord ++ tailWord_883304).sum := by decide
  have hdescent : baseEnd_883304 < baseStart_883304 := by decide
  rcases family_descends (prefixWord ++ tailWord_883304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883338 : List Nat := [3, 1, 2, 3, 4, 1, 1, 2, 1, 2, 3]
def baseStart_883338 : Nat := 118140960795 + 883338 * 2 ^ 59
def prefixEnd_883338 : Nat := 4983230072969 + 3 ^ 40 * 883338 * 2
def baseEnd_883338 : Nat := 453576974381370169712609

theorem tailTrace_883338 : CollatzResearch.WordTrace tailWord_883338 prefixEnd_883338 453576974381370169712609 := by
  unfold tailWord_883338
  simp only [CollatzResearch.WordTrace]
  refine ⟨8054495918456190741190667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21478655782549841976508445 8054495918456190741190667)
  ·
    refine ⟨12081743877684286111786001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8054495918456190741190667 12081743877684286111786001)
    ·
      refine ⟨9061307908263214583839501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12081743877684286111786001 9061307908263214583839501)
      ·
        refine ⟨3397990465598705468939813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9061307908263214583839501 3397990465598705468939813)
        ·
          refine ⟨637123212299757275426215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3397990465598705468939813 637123212299757275426215)
          ·
            refine ⟨955684818449635913139323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 637123212299757275426215 955684818449635913139323)
            ·
              refine ⟨1433527227674453869708985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 955684818449635913139323 1433527227674453869708985)
              ·
                refine ⟨1075145420755840402281739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1433527227674453869708985 1075145420755840402281739)
                ·
                  refine ⟨1612718131133760603422609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1075145420755840402281739 1612718131133760603422609)
                  ·
                    refine ⟨1209538598350320452566957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1612718131133760603422609 1209538598350320452566957)
                    ·
                      refine ⟨453576974381370169712609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1209538598350320452566957 453576974381370169712609)
                      ·
                        rfl

theorem cell23_883338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_883338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_883338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_883338 prefixEnd_883338 := by exact prefixLift 883338
  have htrace : WordTrace (prefixWord ++ tailWord_883338) baseStart_883338 baseEnd_883338 := by
    simpa [prefixWord, tailWord_883338, baseEnd_883338] using wordTrace_append hprefix tailTrace_883338
  have hstable : (prefixWord ++ tailWord_883338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883338).length < 2 ^ (prefixWord ++ tailWord_883338).sum := by decide
  have hdescent : baseEnd_883338 < baseStart_883338 := by decide
  rcases family_descends (prefixWord ++ tailWord_883338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883340 : List Nat := [2, 2, 1, 2, 1, 1, 2, 1, 4, 3, 4]
def baseStart_883340 : Nat := 118140960795 + 883340 * 2 ^ 59
def prefixEnd_883340 : Nat := 4983230072969 + 3 ^ 40 * 883340 * 2
def baseEnd_883340 : Nat := 453578001342679161887599

theorem tailTrace_883340 : CollatzResearch.WordTrace tailWord_883340 prefixEnd_883340 453578001342679161887599 := by
  unfold tailWord_883340
  simp only [CollatzResearch.WordTrace]
  refine ⟨16109028309908758653167737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21478704413211678204223649 16109028309908758653167737)
  ·
    refine ⟨12081771232431568989875803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16109028309908758653167737 12081771232431568989875803)
    ·
      refine ⟨18122656848647353484813705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12081771232431568989875803 18122656848647353484813705)
      ·
        refine ⟨13591992636485515113610279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18122656848647353484813705 13591992636485515113610279)
        ·
          refine ⟨20387988954728272670415419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13591992636485515113610279 20387988954728272670415419)
          ·
            refine ⟨30581983432092409005623129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20387988954728272670415419 30581983432092409005623129)
            ·
              refine ⟨22936487574069306754217347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30581983432092409005623129 22936487574069306754217347)
              ·
                refine ⟨34404731361103960131326021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22936487574069306754217347 34404731361103960131326021)
                ·
                  refine ⟨6450887130206992524623629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34404731361103960131326021 6450887130206992524623629)
                  ·
                    refine ⟨2419082673827622196733861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6450887130206992524623629 2419082673827622196733861)
                    ·
                      refine ⟨453578001342679161887599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2419082673827622196733861 453578001342679161887599)
                      ·
                        rfl

theorem cell23_883340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_883340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_883340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_883340 prefixEnd_883340 := by exact prefixLift 883340
  have htrace : WordTrace (prefixWord ++ tailWord_883340) baseStart_883340 baseEnd_883340 := by
    simpa [prefixWord, tailWord_883340, baseEnd_883340] using wordTrace_append hprefix tailTrace_883340
  have hstable : (prefixWord ++ tailWord_883340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883340).length < 2 ^ (prefixWord ++ tailWord_883340).sum := by decide
  have hdescent : baseEnd_883340 < baseStart_883340 := by decide
  rcases family_descends (prefixWord ++ tailWord_883340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883374 : List Nat := [4, 1, 4, 1, 1, 1, 1, 1, 2, 3, 4]
def baseStart_883374 : Nat := 118140960795 + 883374 * 2 ^ 59
def prefixEnd_883374 : Nat := 4983230072969 + 3 ^ 40 * 883374 * 2
def baseEnd_883374 : Nat := 453595459684932028862443

theorem tailTrace_883374 : CollatzResearch.WordTrace tailWord_883374 prefixEnd_883374 453595459684932028862443 := by
  unfold tailWord_883374
  simp only [CollatzResearch.WordTrace]
  refine ⟨4027412087711792639134147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21479531134462894075382117 4027412087711792639134147)
  ·
    refine ⟨6041118131567688958701221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4027412087711792639134147 6041118131567688958701221)
    ·
      refine ⟨1132709649668941679756479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6041118131567688958701221 1132709649668941679756479)
      ·
        refine ⟨1699064474503412519634719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1132709649668941679756479 1699064474503412519634719)
        ·
          refine ⟨2548596711755118779452079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1699064474503412519634719 2548596711755118779452079)
          ·
            refine ⟨3822895067632678169178119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2548596711755118779452079 3822895067632678169178119)
            ·
              refine ⟨5734342601449017253767179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3822895067632678169178119 5734342601449017253767179)
              ·
                refine ⟨8601513902173525880650769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5734342601449017253767179 8601513902173525880650769)
                ·
                  refine ⟨6451135426630144410488077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8601513902173525880650769 6451135426630144410488077)
                  ·
                    refine ⟨2419175784986304153933029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6451135426630144410488077 2419175784986304153933029)
                    ·
                      refine ⟨453595459684932028862443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2419175784986304153933029 453595459684932028862443)
                      ·
                        rfl

theorem cell23_883374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_883374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_883374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_883374 prefixEnd_883374 := by exact prefixLift 883374
  have htrace : WordTrace (prefixWord ++ tailWord_883374) baseStart_883374 baseEnd_883374 := by
    simpa [prefixWord, tailWord_883374, baseEnd_883374] using wordTrace_append hprefix tailTrace_883374
  have hstable : (prefixWord ++ tailWord_883374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883374).length < 2 ^ (prefixWord ++ tailWord_883374).sum := by decide
  have hdescent : baseEnd_883374 < baseStart_883374 := by decide
  rcases family_descends (prefixWord ++ tailWord_883374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883391 : List Nat := [1, 1, 2, 2, 2, 4, 2, 3, 2, 2, 2]
def baseStart_883391 : Nat := 118140960795 + 883391 * 2 ^ 59
def prefixEnd_883391 : Nat := 4983230072969 + 3 ^ 40 * 883391 * 2
def baseEnd_883391 : Nat := 453604188856058462349865

theorem tailTrace_883391 : CollatzResearch.WordTrace tailWord_883391 prefixEnd_883391 453604188856058462349865 := by
  unfold tailWord_883391
  simp only [CollatzResearch.WordTrace]
  refine ⟨32219916742632753016442027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21479944495088502010961351 32219916742632753016442027)
  ·
    refine ⟨48329875113949129524663041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32219916742632753016442027 48329875113949129524663041)
    ·
      refine ⟨36247406335461847143497281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48329875113949129524663041 36247406335461847143497281)
      ·
        refine ⟨27185554751596385357622961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36247406335461847143497281 27185554751596385357622961)
        ·
          refine ⟨20389166063697289018217221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27185554751596385357622961 20389166063697289018217221)
          ·
            refine ⟨3822968636943241690915729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20389166063697289018217221 3822968636943241690915729)
            ·
              refine ⟨2867226477707431268186797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3822968636943241690915729 2867226477707431268186797)
              ·
                refine ⟨1075209929140286725570049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2867226477707431268186797 1075209929140286725570049)
                ·
                  refine ⟨806407446855215044177537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1075209929140286725570049 806407446855215044177537)
                  ·
                    refine ⟨604805585141411283133153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 806407446855215044177537 604805585141411283133153)
                    ·
                      refine ⟨453604188856058462349865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 604805585141411283133153 453604188856058462349865)
                      ·
                        rfl

theorem cell23_883391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 3, 2, 2, 2].length) (baseStart_883391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_883391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_883391 prefixEnd_883391 := by exact prefixLift 883391
  have htrace : WordTrace (prefixWord ++ tailWord_883391) baseStart_883391 baseEnd_883391 := by
    simpa [prefixWord, tailWord_883391, baseEnd_883391] using wordTrace_append hprefix tailTrace_883391
  have hstable : (prefixWord ++ tailWord_883391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883391).length < 2 ^ (prefixWord ++ tailWord_883391).sum := by decide
  have hdescent : baseEnd_883391 < baseStart_883391 := by decide
  rcases family_descends (prefixWord ++ tailWord_883391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883412 : List Nat := [2, 4, 1, 3, 3, 1, 2, 1, 1, 3, 2]
def baseStart_883412 : Nat := 118140960795 + 883412 * 2 ^ 59
def prefixEnd_883412 : Nat := 4983230072969 + 3 ^ 40 * 883412 * 2
def baseEnd_883412 : Nat := 453614971949802880187269

theorem tailTrace_883412 : CollatzResearch.WordTrace tailWord_883412 prefixEnd_883412 453614971949802880187269 := by
  unfold tailWord_883412
  simp only [CollatzResearch.WordTrace]
  refine ⟨16110341337778336801478245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21480455117037782401970993 16110341337778336801478245)
  ·
    refine ⟨3020689000833438150277171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16110341337778336801478245 3020689000833438150277171)
    ·
      refine ⟨4531033501250157225415757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3020689000833438150277171 4531033501250157225415757)
      ·
        refine ⟨1699137562968808959530909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4531033501250157225415757 1699137562968808959530909)
        ·
          refine ⟨637176586113303359824091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1699137562968808959530909 637176586113303359824091)
          ·
            refine ⟨955764879169955039736137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 637176586113303359824091 955764879169955039736137)
            ·
              refine ⟨716823659377466279802103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 955764879169955039736137 716823659377466279802103)
              ·
                refine ⟨1075235489066199419703155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 716823659377466279802103 1075235489066199419703155)
                ·
                  refine ⟨1612853233599299129554733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1075235489066199419703155 1612853233599299129554733)
                  ·
                    refine ⟨604819962599737173583025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1612853233599299129554733 604819962599737173583025)
                    ·
                      refine ⟨453614971949802880187269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 604819962599737173583025 453614971949802880187269)
                      ·
                        rfl

theorem cell23_883412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_883412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_883412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_883412 prefixEnd_883412 := by exact prefixLift 883412
  have htrace : WordTrace (prefixWord ++ tailWord_883412) baseStart_883412 baseEnd_883412 := by
    simpa [prefixWord, tailWord_883412, baseEnd_883412] using wordTrace_append hprefix tailTrace_883412
  have hstable : (prefixWord ++ tailWord_883412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883412).length < 2 ^ (prefixWord ++ tailWord_883412).sum := by decide
  have hdescent : baseEnd_883412 < baseStart_883412 := by decide
  rcases family_descends (prefixWord ++ tailWord_883412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883437 : List Nat := [1, 5, 1, 2, 1, 1, 2, 1, 1, 1, 7]
def baseStart_883437 : Nat := 118140960795 + 883437 * 2 ^ 59
def prefixEnd_883437 : Nat := 4983230072969 + 3 ^ 40 * 883437 * 2
def baseEnd_883437 : Nat := 453627808966165282374653

theorem tailTrace_883437 : CollatzResearch.WordTrace tailWord_883437 prefixEnd_883437 453627808966165282374653 := by
  unfold tailWord_883437
  simp only [CollatzResearch.WordTrace]
  refine ⟨32221594500466102872616565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21481063000310735248411043 32221594500466102872616565)
  ·
    refine ⟨3020774484418697144307803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32221594500466102872616565 3020774484418697144307803)
    ·
      refine ⟨4531161726628045716461705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3020774484418697144307803 4531161726628045716461705)
      ·
        refine ⟨3398371294971034287346279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4531161726628045716461705 3398371294971034287346279)
        ·
          refine ⟨5097556942456551431019419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3398371294971034287346279 5097556942456551431019419)
          ·
            refine ⟨7646335413684827146529129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5097556942456551431019419 7646335413684827146529129)
            ·
              refine ⟨5734751560263620359896847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7646335413684827146529129 5734751560263620359896847)
              ·
                refine ⟨8602127340395430539845271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5734751560263620359896847 8602127340395430539845271)
                ·
                  refine ⟨12903191010593145809767907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8602127340395430539845271 12903191010593145809767907)
                  ·
                    refine ⟨19354786515889718714651861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12903191010593145809767907 19354786515889718714651861)
                    ·
                      refine ⟨453627808966165282374653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 19354786515889718714651861 453627808966165282374653)
                      ·
                        rfl

theorem cell23_883437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_883437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_883437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_883437 prefixEnd_883437 := by exact prefixLift 883437
  have htrace : WordTrace (prefixWord ++ tailWord_883437) baseStart_883437 baseEnd_883437 := by
    simpa [prefixWord, tailWord_883437, baseEnd_883437] using wordTrace_append hprefix tailTrace_883437
  have hstable : (prefixWord ++ tailWord_883437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883437).length < 2 ^ (prefixWord ++ tailWord_883437).sum := by decide
  have hdescent : baseEnd_883437 < baseStart_883437 := by decide
  rcases family_descends (prefixWord ++ tailWord_883437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883484 : List Nat := [2, 2, 3, 1, 1, 3, 1, 1, 4, 2, 3]
def baseStart_883484 : Nat := 118140960795 + 883484 * 2 ^ 59
def prefixEnd_883484 : Nat := 4983230072969 + 3 ^ 40 * 883484 * 2
def baseEnd_883484 : Nat := 453651942556926598486937

theorem tailTrace_883484 : CollatzResearch.WordTrace tailWord_883484 prefixEnd_883484 453651942556926598486937 := by
  unfold tailWord_883484
  simp only [CollatzResearch.WordTrace]
  refine ⟨16111654365647914949788753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21482205820863886599718337 16111654365647914949788753)
  ·
    refine ⟨12083740774235936212341565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16111654365647914949788753 12083740774235936212341565)
    ·
      refine ⟨4531402790338476079628087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12083740774235936212341565 4531402790338476079628087)
      ·
        refine ⟨6797104185507714119442131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4531402790338476079628087 6797104185507714119442131)
        ·
          refine ⟨10195656278261571179163197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6797104185507714119442131 10195656278261571179163197)
          ·
            refine ⟨3823371104348089192186199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10195656278261571179163197 3823371104348089192186199)
            ·
              refine ⟨5735056656522133788279299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3823371104348089192186199 5735056656522133788279299)
              ·
                refine ⟨8602584984783200682418949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5735056656522133788279299 8602584984783200682418949)
                ·
                  refine ⟨1612984684646850127953553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8602584984783200682418949 1612984684646850127953553)
                  ·
                    refine ⟨1209738513485137595965165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1612984684646850127953553 1209738513485137595965165)
                    ·
                      refine ⟨453651942556926598486937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1209738513485137595965165 453651942556926598486937)
                      ·
                        rfl

theorem cell23_883484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_883484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_883484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_883484 prefixEnd_883484 := by exact prefixLift 883484
  have htrace : WordTrace (prefixWord ++ tailWord_883484) baseStart_883484 baseEnd_883484 := by
    simpa [prefixWord, tailWord_883484, baseEnd_883484] using wordTrace_append hprefix tailTrace_883484
  have hstable : (prefixWord ++ tailWord_883484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883484).length < 2 ^ (prefixWord ++ tailWord_883484).sum := by decide
  have hdescent : baseEnd_883484 < baseStart_883484 := by decide
  rcases family_descends (prefixWord ++ tailWord_883484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883487 : List Nat := [1, 1, 2, 4, 2, 2, 2, 1, 8]
def baseStart_883487 : Nat := 118140960795 + 883487 * 2 ^ 59
def prefixEnd_883487 : Nat := 4983230072969 + 3 ^ 40 * 883487 * 2
def baseEnd_883487 : Nat := 50405942555432231861047

theorem tailTrace_883487 : CollatzResearch.WordTrace tailWord_883487 prefixEnd_883487 50405942555432231861047 := by
  unfold tailWord_883487
  simp only [CollatzResearch.WordTrace]
  refine ⟨32223418150284961411936715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21482278766856640941291143 32223418150284961411936715)
  ·
    refine ⟨48335127225427442117905073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32223418150284961411936715 48335127225427442117905073)
    ·
      refine ⟨36251345419070581588428805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48335127225427442117905073 36251345419070581588428805)
      ·
        refine ⟨6797127266075734047830401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36251345419070581588428805 6797127266075734047830401)
        ·
          refine ⟨5097845449556800535872801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6797127266075734047830401 5097845449556800535872801)
          ·
            refine ⟨3823384087167600401904601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5097845449556800535872801 3823384087167600401904601)
            ·
              refine ⟨2867538065375700301428451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3823384087167600401904601 2867538065375700301428451)
              ·
                refine ⟨4301307098063550452142677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2867538065375700301428451 4301307098063550452142677)
                ·
                  refine ⟨50405942555432231861047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4301307098063550452142677 50405942555432231861047)
                  ·
                    rfl

theorem cell23_883487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 8].length) (baseStart_883487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_883487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_883487 prefixEnd_883487 := by exact prefixLift 883487
  have htrace : WordTrace (prefixWord ++ tailWord_883487) baseStart_883487 baseEnd_883487 := by
    simpa [prefixWord, tailWord_883487, baseEnd_883487] using wordTrace_append hprefix tailTrace_883487
  have hstable : (prefixWord ++ tailWord_883487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883487).length < 2 ^ (prefixWord ++ tailWord_883487).sum := by decide
  have hdescent : baseEnd_883487 < baseStart_883487 := by decide
  rcases family_descends (prefixWord ++ tailWord_883487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883518 : List Nat := [4, 2, 1, 2, 3, 1, 2, 1, 2, 2, 3]
def baseStart_883518 : Nat := 118140960795 + 883518 * 2 ^ 59
def prefixEnd_883518 : Nat := 4983230072969 + 3 ^ 40 * 883518 * 2
def baseEnd_883518 : Nat := 453669400899179465461781

theorem tailTrace_883518 : CollatzResearch.WordTrace tailWord_883518 prefixEnd_883518 453669400899179465461781 := by
  unfold tailWord_883518
  simp only [CollatzResearch.WordTrace]
  refine ⟨4028068601646581713289401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21483032542115102470876805 4028068601646581713289401)
  ·
    refine ⟨3021051451234936284967051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4028068601646581713289401 3021051451234936284967051)
    ·
      refine ⟨4531577176852404427450577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3021051451234936284967051 4531577176852404427450577)
      ·
        refine ⟨3398682882639303320587933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4531577176852404427450577 3398682882639303320587933)
        ·
          refine ⟨1274506080989738745220475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3398682882639303320587933 1274506080989738745220475)
          ·
            refine ⟨1911759121484608117830713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1274506080989738745220475 1911759121484608117830713)
            ·
              refine ⟨1433819341113456088373035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1911759121484608117830713 1433819341113456088373035)
              ·
                refine ⟨2150729011670184132559553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1433819341113456088373035 2150729011670184132559553)
                ·
                  refine ⟨1613046758752638099419665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2150729011670184132559553 1613046758752638099419665)
                  ·
                    refine ⟨1209785069064478574564749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1613046758752638099419665 1209785069064478574564749)
                    ·
                      refine ⟨453669400899179465461781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1209785069064478574564749 453669400899179465461781)
                      ·
                        rfl

theorem cell23_883518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_883518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_883518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_883518 prefixEnd_883518 := by exact prefixLift 883518
  have htrace : WordTrace (prefixWord ++ tailWord_883518) baseStart_883518 baseEnd_883518 := by
    simpa [prefixWord, tailWord_883518, baseEnd_883518] using wordTrace_append hprefix tailTrace_883518
  have hstable : (prefixWord ++ tailWord_883518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883518).length < 2 ^ (prefixWord ++ tailWord_883518).sum := by decide
  have hdescent : baseEnd_883518 < baseStart_883518 := by decide
  rcases family_descends (prefixWord ++ tailWord_883518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883534 : List Nat := [4, 1, 1, 1, 1, 1, 1, 7, 1, 5]
def baseStart_883534 : Nat := 118140960795 + 883534 * 2 ^ 59
def prefixEnd_883534 : Nat := 4983230072969 + 3 ^ 40 * 883534 * 2
def baseEnd_883534 : Nat := 151225872196550467620569

theorem tailTrace_883534 : CollatzResearch.WordTrace tailWord_883534 prefixEnd_883534 151225872196550467620569 := by
  unfold tailWord_883534
  simp only [CollatzResearch.WordTrace]
  refine ⟨4028141547639336054862207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21483421587409792292598437 4028141547639336054862207)
  ·
    refine ⟨6042212321459004082293311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4028141547639336054862207 6042212321459004082293311)
    ·
      refine ⟨9063318482188506123439967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6042212321459004082293311 9063318482188506123439967)
      ·
        refine ⟨13594977723282759185159951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9063318482188506123439967 13594977723282759185159951)
        ·
          refine ⟨20392466584924138777739927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13594977723282759185159951 20392466584924138777739927)
          ·
            refine ⟨30588699877386208166609891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20392466584924138777739927 30588699877386208166609891)
            ·
              refine ⟨45883049816079312249914837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30588699877386208166609891 45883049816079312249914837)
              ·
                refine ⟨1075383980064358880857379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 45883049816079312249914837 1075383980064358880857379)
                ·
                  refine ⟨1613075970096538321286069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1075383980064358880857379 1613075970096538321286069)
                  ·
                    refine ⟨151225872196550467620569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1613075970096538321286069 151225872196550467620569)
                    ·
                      rfl

theorem cell23_883534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 7, 1, 5].length) (baseStart_883534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_883534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_883534 prefixEnd_883534 := by exact prefixLift 883534
  have htrace : WordTrace (prefixWord ++ tailWord_883534) baseStart_883534 baseEnd_883534 := by
    simpa [prefixWord, tailWord_883534, baseEnd_883534] using wordTrace_append hprefix tailTrace_883534
  have hstable : (prefixWord ++ tailWord_883534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883534).length < 2 ^ (prefixWord ++ tailWord_883534).sum := by decide
  have hdescent : baseEnd_883534 < baseStart_883534 := by decide
  rcases family_descends (prefixWord ++ tailWord_883534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883541 : List Nat := [1, 3, 2, 2, 2, 1, 1, 4, 2, 3, 2]
def baseStart_883541 : Nat := 118140960795 + 883541 * 2 ^ 59
def prefixEnd_883541 : Nat := 4983230072969 + 3 ^ 40 * 883541 * 2
def baseEnd_883541 : Nat := 453681210954232875474175

theorem tailTrace_883541 : CollatzResearch.WordTrace tailWord_883541 prefixEnd_883541 453681210954232875474175 := by
  unfold tailWord_883541
  simp only [CollatzResearch.WordTrace]
  refine ⟨32225387692089328634402477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21483591794726219089601651 32225387692089328634402477)
  ·
    refine ⟨12084520384533498237900929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32225387692089328634402477 12084520384533498237900929)
    ·
      refine ⟨9063390288400123678425697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12084520384533498237900929 9063390288400123678425697)
      ·
        refine ⟨6797542716300092758819273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9063390288400123678425697 6797542716300092758819273)
        ·
          refine ⟨5098157037225069569114455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6797542716300092758819273 5098157037225069569114455)
          ·
            refine ⟨7647235555837604353671683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5098157037225069569114455 7647235555837604353671683)
            ·
              refine ⟨11470853333756406530507525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7647235555837604353671683 11470853333756406530507525)
              ·
                refine ⟨2150785000079326224470161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11470853333756406530507525 2150785000079326224470161)
                ·
                  refine ⟨1613088750059494668352621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2150785000079326224470161 1613088750059494668352621)
                  ·
                    refine ⟨604908281272310500632233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1613088750059494668352621 604908281272310500632233)
                    ·
                      refine ⟨453681210954232875474175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 604908281272310500632233 453681210954232875474175)
                      ·
                        rfl

theorem cell23_883541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 4, 2, 3, 2].length) (baseStart_883541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_883541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_883541 prefixEnd_883541 := by exact prefixLift 883541
  have htrace : WordTrace (prefixWord ++ tailWord_883541) baseStart_883541 baseEnd_883541 := by
    simpa [prefixWord, tailWord_883541, baseEnd_883541] using wordTrace_append hprefix tailTrace_883541
  have hstable : (prefixWord ++ tailWord_883541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883541).length < 2 ^ (prefixWord ++ tailWord_883541).sum := by decide
  have hdescent : baseEnd_883541 < baseStart_883541 := by decide
  rcases family_descends (prefixWord ++ tailWord_883541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883564 : List Nat := [2, 2, 1, 1, 4, 1, 4, 1, 1, 6]
def baseStart_883564 : Nat := 118140960795 + 883564 * 2 ^ 59
def prefixEnd_883564 : Nat := 4983230072969 + 3 ^ 40 * 883564 * 2
def baseEnd_883564 : Nat := 151231007003095428495523

theorem tailTrace_883564 : CollatzResearch.WordTrace tailWord_883564 prefixEnd_883564 151231007003095428495523 := by
  unfold tailWord_883564
  simp only [CollatzResearch.WordTrace]
  refine ⟨16113113285503001781244873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21484151047337335708326497 16113113285503001781244873)
  ·
    refine ⟨12084834964127251335933655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16113113285503001781244873 12084834964127251335933655)
    ·
      refine ⟨18127252446190877003900483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12084834964127251335933655 18127252446190877003900483)
      ·
        refine ⟨27190878669286315505850725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18127252446190877003900483 27190878669286315505850725)
        ·
          refine ⟨5098289750491184157347011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27190878669286315505850725 5098289750491184157347011)
          ·
            refine ⟨7647434625736776236020517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5098289750491184157347011 7647434625736776236020517)
            ·
              refine ⟨1433893992325645544253847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7647434625736776236020517 1433893992325645544253847)
              ·
                refine ⟨2150840988488468316380771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1433893992325645544253847 2150840988488468316380771)
                ·
                  refine ⟨3226261482732702474571157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2150840988488468316380771 3226261482732702474571157)
                  ·
                    refine ⟨151231007003095428495523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3226261482732702474571157 151231007003095428495523)
                    ·
                      rfl

theorem cell23_883564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 6].length) (baseStart_883564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_883564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_883564 prefixEnd_883564 := by exact prefixLift 883564
  have htrace : WordTrace (prefixWord ++ tailWord_883564) baseStart_883564 baseEnd_883564 := by
    simpa [prefixWord, tailWord_883564, baseEnd_883564] using wordTrace_append hprefix tailTrace_883564
  have hstable : (prefixWord ++ tailWord_883564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883564).length < 2 ^ (prefixWord ++ tailWord_883564).sum := by decide
  have hdescent : baseEnd_883564 < baseStart_883564 := by decide
  rcases family_descends (prefixWord ++ tailWord_883564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883567 : List Nat := [1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 6]
def baseStart_883567 : Nat := 118140960795 + 883567 * 2 ^ 59
def prefixEnd_883567 : Nat := 4983230072969 + 3 ^ 40 * 883567 * 2
def baseEnd_883567 : Nat := 453694561451249773749055

theorem tailTrace_883567 : CollatzResearch.WordTrace tailWord_883567 prefixEnd_883567 453694561451249773749055 := by
  unfold tailWord_883567
  simp only [CollatzResearch.WordTrace]
  refine ⟨32226335989995135074848955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21484223993330090049899303 32226335989995135074848955)
  ·
    refine ⟨48339503984992702612273433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32226335989995135074848955 48339503984992702612273433)
    ·
      refine ⟨36254627988744526959205075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48339503984992702612273433 36254627988744526959205075)
      ·
        refine ⟨54381941983116790438807613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36254627988744526959205075 54381941983116790438807613)
        ·
          refine ⟨20393228243668796414552855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54381941983116790438807613 20393228243668796414552855)
          ·
            refine ⟨30589842365503194621829283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20393228243668796414552855 30589842365503194621829283)
            ·
              refine ⟨45884763548254791932743925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30589842365503194621829283 45884763548254791932743925)
              ·
                refine ⟨4301696582648886743694743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45884763548254791932743925 4301696582648886743694743)
                ·
                  refine ⟨6452544873973330115542115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4301696582648886743694743 6452544873973330115542115)
                  ·
                    refine ⟨9678817310959995173313173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6452544873973330115542115 9678817310959995173313173)
                    ·
                      refine ⟨453694561451249773749055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9678817310959995173313173 453694561451249773749055)
                      ·
                        rfl

theorem cell23_883567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 6].length) (baseStart_883567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_883567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_883567 prefixEnd_883567 := by exact prefixLift 883567
  have htrace : WordTrace (prefixWord ++ tailWord_883567) baseStart_883567 baseEnd_883567 := by
    simpa [prefixWord, tailWord_883567, baseEnd_883567] using wordTrace_append hprefix tailTrace_883567
  have hstable : (prefixWord ++ tailWord_883567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883567).length < 2 ^ (prefixWord ++ tailWord_883567).sum := by decide
  have hdescent : baseEnd_883567 < baseStart_883567 := by decide
  rcases family_descends (prefixWord ++ tailWord_883567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883571 : List Nat := [1, 1, 1, 2, 2, 1, 5, 1, 5, 2, 2]
def baseStart_883571 : Nat := 118140960795 + 883571 * 2 ^ 59
def prefixEnd_883571 : Nat := 4983230072969 + 3 ^ 40 * 883571 * 2
def baseEnd_883571 : Nat := 453696615373867758099037

theorem tailTrace_883571 : CollatzResearch.WordTrace tailWord_883571 prefixEnd_883571 453696615373867758099037 := by
  unfold tailWord_883571
  simp only [CollatzResearch.WordTrace]
  refine ⟨32226481881980643757994567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21484321254653762505329711 32226481881980643757994567)
  ·
    refine ⟨48339722822970965636991851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32226481881980643757994567 48339722822970965636991851)
    ·
      refine ⟨72509584234456448455487777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48339722822970965636991851 72509584234456448455487777)
      ·
        refine ⟨54382188175842336341615833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72509584234456448455487777 54382188175842336341615833)
        ·
          refine ⟨40786641131881752256211875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54382188175842336341615833 40786641131881752256211875)
          ·
            refine ⟨61179961697822628384317813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40786641131881752256211875 61179961697822628384317813)
            ·
              refine ⟨5735621409170871411029795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61179961697822628384317813 5735621409170871411029795)
              ·
                refine ⟨8603432113756307116544693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5735621409170871411029795 8603432113756307116544693)
                ·
                  refine ⟨806571760664653792176065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8603432113756307116544693 806571760664653792176065)
                  ·
                    refine ⟨604928820498490344132049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 806571760664653792176065 604928820498490344132049)
                    ·
                      refine ⟨453696615373867758099037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 604928820498490344132049 453696615373867758099037)
                      ·
                        rfl

theorem cell23_883571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 5, 2, 2].length) (baseStart_883571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_883571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_883571 prefixEnd_883571 := by exact prefixLift 883571
  have htrace : WordTrace (prefixWord ++ tailWord_883571) baseStart_883571 baseEnd_883571 := by
    simpa [prefixWord, tailWord_883571, baseEnd_883571] using wordTrace_append hprefix tailTrace_883571
  have hstable : (prefixWord ++ tailWord_883571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883571).length < 2 ^ (prefixWord ++ tailWord_883571).sum := by decide
  have hdescent : baseEnd_883571 < baseStart_883571 := by decide
  rcases family_descends (prefixWord ++ tailWord_883571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883594 : List Nat := [3, 1, 2, 4, 1, 2, 10]
def baseStart_883594 : Nat := 118140960795 + 883594 * 2 ^ 59
def prefixEnd_883594 : Nat := 4983230072969 + 3 ^ 40 * 883594 * 2
def baseEnd_883594 : Nat := 5601338585542236643351

theorem tailTrace_883594 : CollatzResearch.WordTrace tailWord_883594 prefixEnd_883594 5601338585542236643351 := by
  unfold tailWord_883594
  simp only [CollatzResearch.WordTrace]
  refine ⟨8056830190224329671520459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21484880507264879124054557 8056830190224329671520459)
  ·
    refine ⟨12085245285336494507280689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8056830190224329671520459 12085245285336494507280689)
    ·
      refine ⟨9063933964002370880460517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12085245285336494507280689 9063933964002370880460517)
      ·
        refine ⟨1699487618250444540086347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9063933964002370880460517 1699487618250444540086347)
        ·
          refine ⟨2549231427375666810129521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1699487618250444540086347 2549231427375666810129521)
          ·
            refine ⟨1911923570531750107597141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2549231427375666810129521 1911923570531750107597141)
            ·
              refine ⟨5601338585542236643351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1911923570531750107597141 5601338585542236643351)
              ·
                rfl

theorem cell23_883594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 10].length) (baseStart_883594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_883594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_883594 prefixEnd_883594 := by exact prefixLift 883594
  have htrace : WordTrace (prefixWord ++ tailWord_883594) baseStart_883594 baseEnd_883594 := by
    simpa [prefixWord, tailWord_883594, baseEnd_883594] using wordTrace_append hprefix tailTrace_883594
  have hstable : (prefixWord ++ tailWord_883594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883594).length < 2 ^ (prefixWord ++ tailWord_883594).sum := by decide
  have hdescent : baseEnd_883594 < baseStart_883594 := by decide
  rcases family_descends (prefixWord ++ tailWord_883594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883605 : List Nat := [1, 3, 2, 1, 1, 4, 2, 4, 1, 2, 2]
def baseStart_883605 : Nat := 118140960795 + 883605 * 2 ^ 59
def prefixEnd_883605 : Nat := 4983230072969 + 3 ^ 40 * 883605 * 2
def baseEnd_883605 : Nat := 453714073716120625073881

theorem tailTrace_883605 : CollatzResearch.WordTrace tailWord_883605 prefixEnd_883605 453714073716120625073881 := by
  unfold tailWord_883605
  simp only [CollatzResearch.WordTrace]
  refine ⟨32227721963857467564732269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21485147975904978376488179 32227721963857467564732269)
  ·
    refine ⟨12085395736446550336774601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32227721963857467564732269 12085395736446550336774601)
    ·
      refine ⟨9064046802334912752580951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12085395736446550336774601 9064046802334912752580951)
      ·
        refine ⟨13596070203502369128871427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9064046802334912752580951 13596070203502369128871427)
        ·
          refine ⟨20394105305253553693307141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13596070203502369128871427 20394105305253553693307141)
          ·
            refine ⟨3823894744735041317495089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20394105305253553693307141 3823894744735041317495089)
            ·
              refine ⟨2867921058551280988121317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3823894744735041317495089 2867921058551280988121317)
              ·
                refine ⟨537735198478365185272747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2867921058551280988121317 537735198478365185272747)
                ·
                  refine ⟨806602797717547777909121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 537735198478365185272747 806602797717547777909121)
                  ·
                    refine ⟨604952098288160833431841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 806602797717547777909121 604952098288160833431841)
                    ·
                      refine ⟨453714073716120625073881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 604952098288160833431841 453714073716120625073881)
                      ·
                        rfl

theorem cell23_883605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 4, 1, 2, 2].length) (baseStart_883605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_883605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_883605 prefixEnd_883605 := by exact prefixLift 883605
  have htrace : WordTrace (prefixWord ++ tailWord_883605) baseStart_883605 baseEnd_883605 := by
    simpa [prefixWord, tailWord_883605, baseEnd_883605] using wordTrace_append hprefix tailTrace_883605
  have hstable : (prefixWord ++ tailWord_883605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883605).length < 2 ^ (prefixWord ++ tailWord_883605).sum := by decide
  have hdescent : baseEnd_883605 < baseStart_883605 := by decide
  rcases family_descends (prefixWord ++ tailWord_883605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883618 : List Nat := [3, 3, 1, 2, 2, 3, 1, 1, 1, 2, 4]
def baseStart_883618 : Nat := 118140960795 + 883618 * 2 ^ 59
def prefixEnd_883618 : Nat := 4983230072969 + 3 ^ 40 * 883618 * 2
def baseEnd_883618 : Nat := 453720748964629074211321

theorem tailTrace_883618 : CollatzResearch.WordTrace tailWord_883618 prefixEnd_883618 453720748964629074211321 := by
  unfold tailWord_883618
  simp only [CollatzResearch.WordTrace]
  refine ⟨8057049028202592696238877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21485464075206913856637005 8057049028202592696238877)
  ·
    refine ⟨3021393385575972261089579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8057049028202592696238877 3021393385575972261089579)
    ·
      refine ⟨4532090078363958391634369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3021393385575972261089579 4532090078363958391634369)
      ·
        refine ⟨3399067558772968793725777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4532090078363958391634369 3399067558772968793725777)
        ·
          refine ⟨2549300669079726595294333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3399067558772968793725777 2549300669079726595294333)
          ·
            refine ⟨955987750904897473235375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2549300669079726595294333 955987750904897473235375)
            ·
              refine ⟨1433981626357346209853063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 955987750904897473235375 1433981626357346209853063)
              ·
                refine ⟨2150972439536019314779595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1433981626357346209853063 2150972439536019314779595)
                ·
                  refine ⟨3226458659304028972169393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2150972439536019314779595 3226458659304028972169393)
                  ·
                    refine ⟨2419843994478021729127045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3226458659304028972169393 2419843994478021729127045)
                    ·
                      refine ⟨453720748964629074211321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2419843994478021729127045 453720748964629074211321)
                      ·
                        rfl

theorem cell23_883618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_883618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_883618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_883618 prefixEnd_883618 := by exact prefixLift 883618
  have htrace : WordTrace (prefixWord ++ tailWord_883618) baseStart_883618 baseEnd_883618 := by
    simpa [prefixWord, tailWord_883618, baseEnd_883618] using wordTrace_append hprefix tailTrace_883618
  have hstable : (prefixWord ++ tailWord_883618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883618).length < 2 ^ (prefixWord ++ tailWord_883618).sum := by decide
  have hdescent : baseEnd_883618 < baseStart_883618 := by decide
  rcases family_descends (prefixWord ++ tailWord_883618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883648 : List Nat := [2, 1, 1, 2, 3, 3, 2, 3, 1, 3, 2]
def baseStart_883648 : Nat := 118140960795 + 883648 * 2 ^ 59
def prefixEnd_883648 : Nat := 4983230072969 + 3 ^ 40 * 883648 * 2
def baseEnd_883648 : Nat := 453736153384263956836183

theorem tailTrace_883648 : CollatzResearch.WordTrace tailWord_883648 prefixEnd_883648 453736153384263956836183 := by
  unfold tailWord_883648
  simp only [CollatzResearch.WordTrace]
  refine ⟨16114645151350842954273799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21486193535134457272365065 16114645151350842954273799)
  ·
    refine ⟨24171967727026264431410699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16114645151350842954273799 24171967727026264431410699)
    ·
      refine ⟨36257951590539396647116049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24171967727026264431410699 36257951590539396647116049)
      ·
        refine ⟨27193463692904547485337037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36257951590539396647116049 27193463692904547485337037)
        ·
          refine ⟨10197548884839205307001389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27193463692904547485337037 10197548884839205307001389)
          ·
            refine ⟨3824080831814701990125521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10197548884839205307001389 3824080831814701990125521)
            ·
              refine ⟨2868060623861026492594141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3824080831814701990125521 2868060623861026492594141)
              ·
                refine ⟨1075522733947884934722803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2868060623861026492594141 1075522733947884934722803)
                ·
                  refine ⟨1613284100921827402084205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1075522733947884934722803 1613284100921827402084205)
                  ·
                    refine ⟨604981537845685275781577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1613284100921827402084205 604981537845685275781577)
                    ·
                      refine ⟨453736153384263956836183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 604981537845685275781577 453736153384263956836183)
                      ·
                        rfl

theorem cell23_883648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 3, 1, 3, 2].length) (baseStart_883648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_883648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_883648 prefixEnd_883648 := by exact prefixLift 883648
  have htrace : WordTrace (prefixWord ++ tailWord_883648) baseStart_883648 baseEnd_883648 := by
    simpa [prefixWord, tailWord_883648, baseEnd_883648] using wordTrace_append hprefix tailTrace_883648
  have hstable : (prefixWord ++ tailWord_883648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883648).length < 2 ^ (prefixWord ++ tailWord_883648).sum := by decide
  have hdescent : baseEnd_883648 < baseStart_883648 := by decide
  rcases family_descends (prefixWord ++ tailWord_883648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883664 : List Nat := [2, 1, 1, 1, 1, 2, 3, 3, 2, 4, 3]
def baseStart_883664 : Nat := 118140960795 + 883664 * 2 ^ 59
def prefixEnd_883664 : Nat := 4983230072969 + 3 ^ 40 * 883664 * 2
def baseEnd_883664 : Nat := 453744369074735894236109

theorem tailTrace_883664 : CollatzResearch.WordTrace tailWord_883664 prefixEnd_883664 453744369074735894236109 := by
  unfold tailWord_883664
  simp only [CollatzResearch.WordTrace]
  refine ⟨16114936935321860320565023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21486582580429147094086697 16114936935321860320565023)
  ·
    refine ⟨24172405402982790480847535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16114936935321860320565023 24172405402982790480847535)
    ·
      refine ⟨36258608104474185721271303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24172405402982790480847535 36258608104474185721271303)
      ·
        refine ⟨54387912156711278581906955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36258608104474185721271303 54387912156711278581906955)
        ·
          refine ⟨81581868235066917872860433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54387912156711278581906955 81581868235066917872860433)
          ·
            refine ⟨61186401176300188404645325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81581868235066917872860433 61186401176300188404645325)
            ·
              refine ⟨22944900441112570651741997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61186401176300188404645325 22944900441112570651741997)
              ·
                refine ⟨8604337665417213994403249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22944900441112570651741997 8604337665417213994403249)
                ·
                  refine ⟨6453253249062910495802437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8604337665417213994403249 6453253249062910495802437)
                  ·
                    refine ⟨1209984984199295717962957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6453253249062910495802437 1209984984199295717962957)
                    ·
                      refine ⟨453744369074735894236109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1209984984199295717962957 453744369074735894236109)
                      ·
                        rfl

theorem cell23_883664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 2, 4, 3].length) (baseStart_883664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_883664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_883664 prefixEnd_883664 := by exact prefixLift 883664
  have htrace : WordTrace (prefixWord ++ tailWord_883664) baseStart_883664 baseEnd_883664 := by
    simpa [prefixWord, tailWord_883664, baseEnd_883664] using wordTrace_append hprefix tailTrace_883664
  have hstable : (prefixWord ++ tailWord_883664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883664).length < 2 ^ (prefixWord ++ tailWord_883664).sum := by decide
  have hdescent : baseEnd_883664 < baseStart_883664 := by decide
  rcases family_descends (prefixWord ++ tailWord_883664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883682 : List Nat := [3, 3, 3, 1, 1, 1, 3, 2, 1, 3, 2]
def baseStart_883682 : Nat := 118140960795 + 883682 * 2 ^ 59
def prefixEnd_883682 : Nat := 4983230072969 + 3 ^ 40 * 883682 * 2
def baseEnd_883682 : Nat := 453753611726516823811027

theorem tailTrace_883682 : CollatzResearch.WordTrace tailWord_883682 prefixEnd_883682 453753611726516823811027 := by
  unfold tailWord_883682
  simp only [CollatzResearch.WordTrace]
  refine ⟨8057632596144627428821325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21487020256385673143523533 8057632596144627428821325)
  ·
    refine ⟨3021612223554235285807997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8057632596144627428821325 3021612223554235285807997)
    ·
      refine ⟨1133104583832838232177999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3021612223554235285807997 1133104583832838232177999)
      ·
        refine ⟨1699656875749257348266999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1133104583832838232177999 1699656875749257348266999)
        ·
          refine ⟨2549485313623886022400499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1699656875749257348266999 2549485313623886022400499)
          ·
            refine ⟨3824227970435829033600749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2549485313623886022400499 3824227970435829033600749)
            ·
              refine ⟨1434085488913435887600281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3824227970435829033600749 1434085488913435887600281)
              ·
                refine ⟨1075564116685076915700211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1434085488913435887600281 1075564116685076915700211)
                ·
                  refine ⟨1613346175027615373550317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1075564116685076915700211 1613346175027615373550317)
                  ·
                    refine ⟨605004815635355765081369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1613346175027615373550317 605004815635355765081369)
                    ·
                      refine ⟨453753611726516823811027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 605004815635355765081369 453753611726516823811027)
                      ·
                        rfl

theorem cell23_883682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_883682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_883682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_883682 prefixEnd_883682 := by exact prefixLift 883682
  have htrace : WordTrace (prefixWord ++ tailWord_883682) baseStart_883682 baseEnd_883682 := by
    simpa [prefixWord, tailWord_883682, baseEnd_883682] using wordTrace_append hprefix tailTrace_883682
  have hstable : (prefixWord ++ tailWord_883682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883682).length < 2 ^ (prefixWord ++ tailWord_883682).sum := by decide
  have hdescent : baseEnd_883682 < baseStart_883682 := by decide
  rcases family_descends (prefixWord ++ tailWord_883682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883748 : List Nat := [2, 3, 1, 4, 1, 1, 3, 1, 2, 5]
def baseStart_883748 : Nat := 118140960795 + 883748 * 2 ^ 59
def prefixEnd_883748 : Nat := 4983230072969 + 3 ^ 40 * 883748 * 2
def baseEnd_883748 : Nat := 151262500483237855195241

theorem tailTrace_883748 : CollatzResearch.WordTrace tailWord_883748 prefixEnd_883748 151262500483237855195241 := by
  unfold tailWord_883748
  simp only [CollatzResearch.WordTrace]
  refine ⟨16116468801169701493593949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21488625068226268658125265 16116468801169701493593949)
  ·
    refine ⟨6043675800438638060097731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16116468801169701493593949 6043675800438638060097731)
    ·
      refine ⟨9065513700657957090146597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6043675800438638060097731 9065513700657957090146597)
      ·
        refine ⟨1699783818873366954402487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9065513700657957090146597 1699783818873366954402487)
        ·
          refine ⟨2549675728310050431603731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1699783818873366954402487 2549675728310050431603731)
          ·
            refine ⟨3824513592465075647405597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2549675728310050431603731 3824513592465075647405597)
            ·
              refine ⟨1434192597174403367777099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3824513592465075647405597 1434192597174403367777099)
              ·
                refine ⟨2151288895761605051665649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1434192597174403367777099 2151288895761605051665649)
                ·
                  refine ⟨1613466671821203788749237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2151288895761605051665649 1613466671821203788749237)
                  ·
                    refine ⟨151262500483237855195241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1613466671821203788749237 151262500483237855195241)
                    ·
                      rfl

theorem cell23_883748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 1, 2, 5].length) (baseStart_883748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_883748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_883748 prefixEnd_883748 := by exact prefixLift 883748
  have htrace : WordTrace (prefixWord ++ tailWord_883748) baseStart_883748 baseEnd_883748 := by
    simpa [prefixWord, tailWord_883748, baseEnd_883748] using wordTrace_append hprefix tailTrace_883748
  have hstable : (prefixWord ++ tailWord_883748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883748).length < 2 ^ (prefixWord ++ tailWord_883748).sum := by decide
  have hdescent : baseEnd_883748 < baseStart_883748 := by decide
  rcases family_descends (prefixWord ++ tailWord_883748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883761 : List Nat := [1, 2, 2, 3, 1, 2, 1, 2, 5, 4]
def baseStart_883761 : Nat := 118140960795 + 883761 * 2 ^ 59
def prefixEnd_883761 : Nat := 4983230072969 + 3 ^ 40 * 883761 * 2
def baseEnd_883761 : Nat := 151264725566074004907721

theorem tailTrace_883761 : CollatzResearch.WordTrace tailWord_883761 prefixEnd_883761 151264725566074004907721 := by
  unfold tailWord_883761
  simp only [CollatzResearch.WordTrace]
  refine ⟨32233411751292306207411137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21488941167528204138274091 32233411751292306207411137)
  ·
    refine ⟨24175058813469229655558353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32233411751292306207411137 24175058813469229655558353)
    ·
      refine ⟨18131294110101922241668765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24175058813469229655558353 18131294110101922241668765)
      ·
        refine ⟨6799235291288220840625787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18131294110101922241668765 6799235291288220840625787)
        ·
          refine ⟨10198852936932331260938681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6799235291288220840625787 10198852936932331260938681)
          ·
            refine ⟨7649139702699248445704011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10198852936932331260938681 7649139702699248445704011)
            ·
              refine ⟨11473709554048872668556017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7649139702699248445704011 11473709554048872668556017)
              ·
                refine ⟨8605282165536654501417013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11473709554048872668556017 8605282165536654501417013)
                ·
                  refine ⟨806745203019061359507845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8605282165536654501417013 806745203019061359507845)
                  ·
                    refine ⟨151264725566074004907721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 806745203019061359507845 151264725566074004907721)
                    ·
                      rfl

theorem cell23_883761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 5, 4].length) (baseStart_883761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_883761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_883761 prefixEnd_883761 := by exact prefixLift 883761
  have htrace : WordTrace (prefixWord ++ tailWord_883761) baseStart_883761 baseEnd_883761 := by
    simpa [prefixWord, tailWord_883761, baseEnd_883761] using wordTrace_append hprefix tailTrace_883761
  have hstable : (prefixWord ++ tailWord_883761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883761).length < 2 ^ (prefixWord ++ tailWord_883761).sum := by decide
  have hdescent : baseEnd_883761 < baseStart_883761 := by decide
  rcases family_descends (prefixWord ++ tailWord_883761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883768 : List Nat := [2, 1, 2, 1, 5, 1, 1, 2, 2, 4, 2]
def baseStart_883768 : Nat := 118140960795 + 883768 * 2 ^ 59
def prefixEnd_883768 : Nat := 4983230072969 + 3 ^ 40 * 883768 * 2
def baseEnd_883768 : Nat := 453797771062803487335631

theorem tailTrace_883768 : CollatzResearch.WordTrace tailWord_883768 prefixEnd_883768 453797771062803487335631 := by
  unfold tailWord_883768
  simp only [CollatzResearch.WordTrace]
  refine ⟨16116833531133473201457979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21489111374844630935277305 16116833531133473201457979)
  ·
    refine ⟨24175250296700209802186969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16116833531133473201457979 24175250296700209802186969)
    ·
      refine ⟨18131437722525157351640227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24175250296700209802186969 18131437722525157351640227)
      ·
        refine ⟨27197156583787736027460341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18131437722525157351640227 27197156583787736027460341)
        ·
          refine ⟨2549733429730100252574407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27197156583787736027460341 2549733429730100252574407)
          ·
            refine ⟨3824600144595150378861611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2549733429730100252574407 3824600144595150378861611)
            ·
              refine ⟨5736900216892725568292417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3824600144595150378861611 5736900216892725568292417)
              ·
                refine ⟨4302675162669544176219313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5736900216892725568292417 4302675162669544176219313)
                ·
                  refine ⟨3227006372002158132164485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4302675162669544176219313 3227006372002158132164485)
                  ·
                    refine ⟨605063694750404649780841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3227006372002158132164485 605063694750404649780841)
                    ·
                      refine ⟨453797771062803487335631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 605063694750404649780841 453797771062803487335631)
                      ·
                        rfl

theorem cell23_883768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 2, 4, 2].length) (baseStart_883768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_883768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_883768 prefixEnd_883768 := by exact prefixLift 883768
  have htrace : WordTrace (prefixWord ++ tailWord_883768) baseStart_883768 baseEnd_883768 := by
    simpa [prefixWord, tailWord_883768, baseEnd_883768] using wordTrace_append hprefix tailTrace_883768
  have hstable : (prefixWord ++ tailWord_883768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883768).length < 2 ^ (prefixWord ++ tailWord_883768).sum := by decide
  have hdescent : baseEnd_883768 < baseStart_883768 := by decide
  rcases family_descends (prefixWord ++ tailWord_883768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883829 : List Nat := [1, 3, 4, 3, 2, 1, 1, 1, 3, 4]
def baseStart_883829 : Nat := 118140960795 + 883829 * 2 ^ 59
def prefixEnd_883829 : Nat := 4983230072969 + 3 ^ 40 * 883829 * 2
def baseEnd_883829 : Nat := 151276364460909249557617

theorem tailTrace_883829 : CollatzResearch.WordTrace tailWord_883829 prefixEnd_883829 151276364460909249557617 := by
  unfold tailWord_883829
  simp only [CollatzResearch.WordTrace]
  refine ⟨32235891915045953820886541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21490594610030635880591027 32235891915045953820886541)
  ·
    refine ⟨12088459468142232682832453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32235891915045953820886541 12088459468142232682832453)
    ·
      refine ⟨2266586150276668628031085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12088459468142232682832453 2266586150276668628031085)
      ·
        refine ⟨849969806353750735511657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2266586150276668628031085 849969806353750735511657)
        ·
          refine ⟨637477354765313051633743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 849969806353750735511657 637477354765313051633743)
          ·
            refine ⟨956216032147969577450615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 637477354765313051633743 956216032147969577450615)
            ·
              refine ⟨1434324048221954366175923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 956216032147969577450615 1434324048221954366175923)
              ·
                refine ⟨2151486072332931549263885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1434324048221954366175923 2151486072332931549263885)
                ·
                  refine ⟨806807277124849330973957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2151486072332931549263885 806807277124849330973957)
                  ·
                    refine ⟨151276364460909249557617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 806807277124849330973957 151276364460909249557617)
                    ·
                      rfl

theorem cell23_883829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_883829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_883829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_883829 prefixEnd_883829 := by exact prefixLift 883829
  have htrace : WordTrace (prefixWord ++ tailWord_883829) baseStart_883829 baseEnd_883829 := by
    simpa [prefixWord, tailWord_883829, baseEnd_883829] using wordTrace_append hprefix tailTrace_883829
  have hstable : (prefixWord ++ tailWord_883829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883829).length < 2 ^ (prefixWord ++ tailWord_883829).sum := by decide
  have hdescent : baseEnd_883829 < baseStart_883829 := by decide
  rcases family_descends (prefixWord ++ tailWord_883829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883835 : List Nat := [1, 1, 1, 1, 1, 4, 1, 8, 1, 1, 3]
def baseStart_883835 : Nat := 118140960795 + 883835 * 2 ^ 59
def prefixEnd_883835 : Nat := 4983230072969 + 3 ^ 40 * 883835 * 2
def baseEnd_883835 : Nat := 453832174266654725197823

theorem tailTrace_883835 : CollatzResearch.WordTrace tailWord_883835 prefixEnd_883835 453832174266654725197823 := by
  unfold tailWord_883835
  simp only [CollatzResearch.WordTrace]
  refine ⟨32236110753024216845604959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21490740502016144563736639 32236110753024216845604959)
  ·
    refine ⟨48354166129536325268407439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32236110753024216845604959 48354166129536325268407439)
    ·
      refine ⟨72531249194304487902611159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48354166129536325268407439 72531249194304487902611159)
      ·
        refine ⟨108796873791456731853916739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72531249194304487902611159 108796873791456731853916739)
        ·
          refine ⟨163195310687185097780875109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108796873791456731853916739 163195310687185097780875109)
          ·
            refine ⟨30599120753847205833914083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 163195310687185097780875109 30599120753847205833914083)
            ·
              refine ⟨45898681130770808750871125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30599120753847205833914083 45898681130770808750871125)
              ·
                refine ⟨537875169501220415049271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 45898681130770808750871125 537875169501220415049271)
                ·
                  refine ⟨806812754251830622573907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 537875169501220415049271 806812754251830622573907)
                  ·
                    refine ⟨1210219131377745933860861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 806812754251830622573907 1210219131377745933860861)
                    ·
                      refine ⟨453832174266654725197823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1210219131377745933860861 453832174266654725197823)
                      ·
                        rfl

theorem cell23_883835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 8, 1, 1, 3].length) (baseStart_883835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_883835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_883835 prefixEnd_883835 := by exact prefixLift 883835
  have htrace : WordTrace (prefixWord ++ tailWord_883835) baseStart_883835 baseEnd_883835 := by
    simpa [prefixWord, tailWord_883835, baseEnd_883835] using wordTrace_append hprefix tailTrace_883835
  have hstable : (prefixWord ++ tailWord_883835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883835).length < 2 ^ (prefixWord ++ tailWord_883835).sum := by decide
  have hdescent : baseEnd_883835 < baseStart_883835 := by decide
  rcases family_descends (prefixWord ++ tailWord_883835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883868 : List Nat := [2, 2, 3, 2, 1, 3, 1, 2, 1, 6]
def baseStart_883868 : Nat := 118140960795 + 883868 * 2 ^ 59
def prefixEnd_883868 : Nat := 4983230072969 + 3 ^ 40 * 883868 * 2
def baseEnd_883868 : Nat := 151283039709417698695057

theorem tailTrace_883868 : CollatzResearch.WordTrace tailWord_883868 prefixEnd_883868 151283039709417698695057 := by
  unfold tailWord_883868
  simp only [CollatzResearch.WordTrace]
  refine ⟨16118657180952331740778129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21491542907936442321037505 16118657180952331740778129)
  ·
    refine ⟨12088992885714248805583597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16118657180952331740778129 12088992885714248805583597)
    ·
      refine ⟨4533372332142843302093849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12088992885714248805583597 4533372332142843302093849)
      ·
        refine ⟨3400029249107132476570387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4533372332142843302093849 3400029249107132476570387)
        ·
          refine ⟨5100043873660698714855581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3400029249107132476570387 5100043873660698714855581)
          ·
            refine ⟨1912516452622762018070843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5100043873660698714855581 1912516452622762018070843)
            ·
              refine ⟨2868774678934143027106265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1912516452622762018070843 2868774678934143027106265)
              ·
                refine ⟨2151581009200607270329699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2868774678934143027106265 2151581009200607270329699)
                ·
                  refine ⟨3227371513800910905494549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2151581009200607270329699 3227371513800910905494549)
                  ·
                    refine ⟨151283039709417698695057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3227371513800910905494549 151283039709417698695057)
                    ·
                      rfl

theorem cell23_883868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_883868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_883868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_883868 prefixEnd_883868 := by exact prefixLift 883868
  have htrace : WordTrace (prefixWord ++ tailWord_883868) baseStart_883868 baseEnd_883868 := by
    simpa [prefixWord, tailWord_883868, baseEnd_883868] using wordTrace_append hprefix tailTrace_883868
  have hstable : (prefixWord ++ tailWord_883868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883868).length < 2 ^ (prefixWord ++ tailWord_883868).sum := by decide
  have hdescent : baseEnd_883868 < baseStart_883868 := by decide
  rcases family_descends (prefixWord ++ tailWord_883868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883901 : List Nat := [1, 4, 1, 2, 1, 1, 2, 1, 2, 2, 6]
def baseStart_883901 : Nat := 118140960795 + 883901 * 2 ^ 59
def prefixEnd_883901 : Nat := 4983230072969 + 3 ^ 40 * 883901 * 2
def baseEnd_883901 : Nat := 453866063989851466972519

theorem tailTrace_883901 : CollatzResearch.WordTrace tailWord_883901 prefixEnd_883901 453866063989851466972519 := by
  unfold tailWord_883901
  simp only [CollatzResearch.WordTrace]
  refine ⟨32238517970785110117507557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21492345313856740078338371 32238517970785110117507557)
  ·
    refine ⟨6044722119522208147032667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32238517970785110117507557 6044722119522208147032667)
    ·
      refine ⟨9067083179283312220549001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6044722119522208147032667 9067083179283312220549001)
      ·
        refine ⟨6800312384462484165411751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9067083179283312220549001 6800312384462484165411751)
        ·
          refine ⟨10200468576693726248117627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6800312384462484165411751 10200468576693726248117627)
          ·
            refine ⟨15300702865040589372176441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10200468576693726248117627 15300702865040589372176441)
            ·
              refine ⟨11475527148780442029132331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15300702865040589372176441 11475527148780442029132331)
              ·
                refine ⟨17213290723170663043698497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11475527148780442029132331 17213290723170663043698497)
                ·
                  refine ⟨12909968042377997282773873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17213290723170663043698497 12909968042377997282773873)
                  ·
                    refine ⟨9682476031783497962080405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12909968042377997282773873 9682476031783497962080405)
                    ·
                      refine ⟨453866063989851466972519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9682476031783497962080405 453866063989851466972519)
                      ·
                        rfl

theorem cell23_883901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_883901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_883901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_883901 prefixEnd_883901 := by exact prefixLift 883901
  have htrace : WordTrace (prefixWord ++ tailWord_883901) baseStart_883901 baseEnd_883901 := by
    simpa [prefixWord, tailWord_883901, baseEnd_883901] using wordTrace_append hprefix tailTrace_883901
  have hstable : (prefixWord ++ tailWord_883901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883901).length < 2 ^ (prefixWord ++ tailWord_883901).sum := by decide
  have hdescent : baseEnd_883901 < baseStart_883901 := by decide
  rcases family_descends (prefixWord ++ tailWord_883901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883905 : List Nat := [1, 2, 6, 1, 1, 1, 1, 3, 1, 2, 4]
def baseStart_883905 : Nat := 118140960795 + 883905 * 2 ^ 59
def prefixEnd_883905 : Nat := 4983230072969 + 3 ^ 40 * 883905 * 2
def baseEnd_883905 : Nat := 453868117912469451322501

theorem tailTrace_883905 : CollatzResearch.WordTrace tailWord_883905 prefixEnd_883905 453868117912469451322501 := by
  unfold tailWord_883905
  simp only [CollatzResearch.WordTrace]
  refine ⟨32238663862770618800653169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21492442575180412533768779 32238663862770618800653169)
  ·
    refine ⟨24178997897077964100489877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32238663862770618800653169 24178997897077964100489877)
    ·
      refine ⟨1133390526425529567210463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 24178997897077964100489877 1133390526425529567210463)
      ·
        refine ⟨1700085789638294350815695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1133390526425529567210463 1700085789638294350815695)
        ·
          refine ⟨2550128684457441526223543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1700085789638294350815695 2550128684457441526223543)
          ·
            refine ⟨3825193026686162289335315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2550128684457441526223543 3825193026686162289335315)
            ·
              refine ⟨5737789540029243434002973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3825193026686162289335315 5737789540029243434002973)
              ·
                refine ⟨2151671077510966287751115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5737789540029243434002973 2151671077510966287751115)
                ·
                  refine ⟨3227506616266449431626673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2151671077510966287751115 3227506616266449431626673)
                  ·
                    refine ⟨2420629962199837073720005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3227506616266449431626673 2420629962199837073720005)
                    ·
                      refine ⟨453868117912469451322501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2420629962199837073720005 453868117912469451322501)
                      ·
                        rfl

theorem cell23_883905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_883905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_883905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_883905 prefixEnd_883905 := by exact prefixLift 883905
  have htrace : WordTrace (prefixWord ++ tailWord_883905) baseStart_883905 baseEnd_883905 := by
    simpa [prefixWord, tailWord_883905, baseEnd_883905] using wordTrace_append hprefix tailTrace_883905
  have hstable : (prefixWord ++ tailWord_883905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883905).length < 2 ^ (prefixWord ++ tailWord_883905).sum := by decide
  have hdescent : baseEnd_883905 < baseStart_883905 := by decide
  rcases family_descends (prefixWord ++ tailWord_883905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883921 : List Nat := [1, 2, 2, 1, 2, 2, 1, 3, 2, 2, 5]
def baseStart_883921 : Nat := 118140960795 + 883921 * 2 ^ 59
def prefixEnd_883921 : Nat := 4983230072969 + 3 ^ 40 * 883921 * 2
def baseEnd_883921 : Nat := 453876333602941388722427

theorem tailTrace_883921 : CollatzResearch.WordTrace tailWord_883921 prefixEnd_883921 453876333602941388722427 := by
  unfold tailWord_883921
  simp only [CollatzResearch.WordTrace]
  refine ⟨32239247430712653533235617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21492831620475102355490411 32239247430712653533235617)
  ·
    refine ⟨24179435573034490149926713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32239247430712653533235617 24179435573034490149926713)
    ·
      refine ⟨18134576679775867612445035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24179435573034490149926713 18134576679775867612445035)
      ·
        refine ⟨27201865019663801418667553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18134576679775867612445035 27201865019663801418667553)
        ·
          refine ⟨20401398764747851064000665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27201865019663801418667553 20401398764747851064000665)
          ·
            refine ⟨15301049073560888298000499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20401398764747851064000665 15301049073560888298000499)
            ·
              refine ⟨22951573610341332447000749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15301049073560888298000499 22951573610341332447000749)
              ·
                refine ⟨8606840103877999667625281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22951573610341332447000749 8606840103877999667625281)
                ·
                  refine ⟨6455130077908499750718961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8606840103877999667625281 6455130077908499750718961)
                  ·
                    refine ⟨4841347558431374813039221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6455130077908499750718961 4841347558431374813039221)
                    ·
                      refine ⟨453876333602941388722427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4841347558431374813039221 453876333602941388722427)
                      ·
                        rfl

theorem cell23_883921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 2, 5].length) (baseStart_883921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_883921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_883921 prefixEnd_883921 := by exact prefixLift 883921
  have htrace : WordTrace (prefixWord ++ tailWord_883921) baseStart_883921 baseEnd_883921 := by
    simpa [prefixWord, tailWord_883921, baseEnd_883921] using wordTrace_append hprefix tailTrace_883921
  have hstable : (prefixWord ++ tailWord_883921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883921).length < 2 ^ (prefixWord ++ tailWord_883921).sum := by decide
  have hdescent : baseEnd_883921 < baseStart_883921 := by decide
  rcases family_descends (prefixWord ++ tailWord_883921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883925 : List Nat := [1, 3, 2, 4, 1, 1, 2, 2, 1, 3, 3]
def baseStart_883925 : Nat := 118140960795 + 883925 * 2 ^ 59
def prefixEnd_883925 : Nat := 4983230072969 + 3 ^ 40 * 883925 * 2
def baseEnd_883925 : Nat := 453878387525559373072409

theorem tailTrace_883925 : CollatzResearch.WordTrace tailWord_883925 prefixEnd_883925 453878387525559373072409 := by
  unfold tailWord_883925
  simp only [CollatzResearch.WordTrace]
  refine ⟨32239393322698162216381229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21492928881798774810920819 32239393322698162216381229)
  ·
    refine ⟨12089772496011810831142961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32239393322698162216381229 12089772496011810831142961)
    ·
      refine ⟨9067329372008858123357221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12089772496011810831142961 9067329372008858123357221)
      ·
        refine ⟨1700124257251660898129479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9067329372008858123357221 1700124257251660898129479)
        ·
          refine ⟨2550186385877491347194219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1700124257251660898129479 2550186385877491347194219)
          ·
            refine ⟨3825279578816237020791329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2550186385877491347194219 3825279578816237020791329)
            ·
              refine ⟨2868959684112177765593497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3825279578816237020791329 2868959684112177765593497)
              ·
                refine ⟨2151719763084133324195123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2868959684112177765593497 2151719763084133324195123)
                ·
                  refine ⟨3227579644626199986292685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2151719763084133324195123 3227579644626199986292685)
                  ·
                    refine ⟨1210342366734824994859757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3227579644626199986292685 1210342366734824994859757)
                    ·
                      refine ⟨453878387525559373072409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1210342366734824994859757 453878387525559373072409)
                      ·
                        rfl

theorem cell23_883925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_883925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_883925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_883925 prefixEnd_883925 := by exact prefixLift 883925
  have htrace : WordTrace (prefixWord ++ tailWord_883925) baseStart_883925 baseEnd_883925 := by
    simpa [prefixWord, tailWord_883925, baseEnd_883925] using wordTrace_append hprefix tailTrace_883925
  have hstable : (prefixWord ++ tailWord_883925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883925).length < 2 ^ (prefixWord ++ tailWord_883925).sum := by decide
  have hdescent : baseEnd_883925 < baseStart_883925 := by decide
  rcases family_descends (prefixWord ++ tailWord_883925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883926 : List Nat := [5, 2, 1, 2, 2, 2, 2, 1, 1, 1, 4]
def baseStart_883926 : Nat := 118140960795 + 883926 * 2 ^ 59
def prefixEnd_883926 : Nat := 4983230072969 + 3 ^ 40 * 883926 * 2
def baseEnd_883926 : Nat := 453878901006213869159905

theorem tailTrace_883926 : CollatzResearch.WordTrace tailWord_883926 prefixEnd_883926 453878901006213869159905 := by
  unfold tailWord_883926
  simp only [CollatzResearch.WordTrace]
  refine ⟨2014964362230908711697977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21492953197129692924778421 2014964362230908711697977)
  ·
    refine ⟨1511223271673181533773483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2014964362230908711697977 1511223271673181533773483)
    ·
      refine ⟨2266834907509772300660225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1511223271673181533773483 2266834907509772300660225)
      ·
        refine ⟨1700126180632329225495169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2266834907509772300660225 1700126180632329225495169)
        ·
          refine ⟨1275094635474246919121377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1700126180632329225495169 1275094635474246919121377)
          ·
            refine ⟨956320976605685189341033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1275094635474246919121377 956320976605685189341033)
            ·
              refine ⟨717240732454263892005775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 956320976605685189341033 717240732454263892005775)
              ·
                refine ⟨1075861098681395838008663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 717240732454263892005775 1075861098681395838008663)
                ·
                  refine ⟨1613791648022093757012995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1075861098681395838008663 1613791648022093757012995)
                  ·
                    refine ⟨2420687472033140635519493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1613791648022093757012995 2420687472033140635519493)
                    ·
                      refine ⟨453878901006213869159905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2420687472033140635519493 453878901006213869159905)
                      ·
                        rfl

theorem cell23_883926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_883926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_883926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_883926 prefixEnd_883926 := by exact prefixLift 883926
  have htrace : WordTrace (prefixWord ++ tailWord_883926) baseStart_883926 baseEnd_883926 := by
    simpa [prefixWord, tailWord_883926, baseEnd_883926] using wordTrace_append hprefix tailTrace_883926
  have hstable : (prefixWord ++ tailWord_883926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883926).length < 2 ^ (prefixWord ++ tailWord_883926).sum := by decide
  have hdescent : baseEnd_883926 < baseStart_883926 := by decide
  rcases family_descends (prefixWord ++ tailWord_883926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883956 : List Nat := [2, 6, 1, 2, 1, 2, 1, 1, 1, 2, 4]
def baseStart_883956 : Nat := 118140960795 + 883956 * 2 ^ 59
def prefixEnd_883956 : Nat := 4983230072969 + 3 ^ 40 * 883956 * 2
def baseEnd_883956 : Nat := 453894305425848751784767

theorem tailTrace_883956 : CollatzResearch.WordTrace tailWord_883956 prefixEnd_883956 453894305425848751784767 := by
  unfold tailWord_883956
  simp only [CollatzResearch.WordTrace]
  refine ⟨16120261992792927255379861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21493682657057236340506481 16120261992792927255379861)
  ·
    refine ⟨755637280912168465095931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 16120261992792927255379861 755637280912168465095931)
    ·
      refine ⟨1133455921368252697643897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 755637280912168465095931 1133455921368252697643897)
      ·
        refine ⟨850091941026189523232923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1133455921368252697643897 850091941026189523232923)
        ·
          refine ⟨1275137911539284284849385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 850091941026189523232923 1275137911539284284849385)
          ·
            refine ⟨956353433654463213637039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1275137911539284284849385 956353433654463213637039)
            ·
              refine ⟨1434530150481694820455559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 956353433654463213637039 1434530150481694820455559)
              ·
                refine ⟨2151795225722542230683339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1434530150481694820455559 2151795225722542230683339)
                ·
                  refine ⟨3227692838583813346025009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2151795225722542230683339 3227692838583813346025009)
                  ·
                    refine ⟨2420769628937860009518757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3227692838583813346025009 2420769628937860009518757)
                    ·
                      refine ⟨453894305425848751784767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2420769628937860009518757 453894305425848751784767)
                      ·
                        rfl

theorem cell23_883956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_883956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_883956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_883956 prefixEnd_883956 := by exact prefixLift 883956
  have htrace : WordTrace (prefixWord ++ tailWord_883956) baseStart_883956 baseEnd_883956 := by
    simpa [prefixWord, tailWord_883956, baseEnd_883956] using wordTrace_append hprefix tailTrace_883956
  have hstable : (prefixWord ++ tailWord_883956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883956).length < 2 ^ (prefixWord ++ tailWord_883956).sum := by decide
  have hdescent : baseEnd_883956 < baseStart_883956 := by decide
  rcases family_descends (prefixWord ++ tailWord_883956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883982 : List Nat := [4, 1, 1, 2, 1, 3, 1, 2, 4, 2, 2]
def baseStart_883982 : Nat := 118140960795 + 883982 * 2 ^ 59
def prefixEnd_883982 : Nat := 4983230072969 + 3 ^ 40 * 883982 * 2
def baseEnd_883982 : Nat := 453907655922865650059647

theorem tailTrace_883982 : CollatzResearch.WordTrace tailWord_883982 prefixEnd_883982 453907655922865650059647 := by
  unfold tailWord_883982
  simp only [CollatzResearch.WordTrace]
  refine ⟨4030184035436457618900775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21494314855661107300804133 4030184035436457618900775)
  ·
    refine ⟨6045276053154686428351163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4030184035436457618900775 6045276053154686428351163)
    ·
      refine ⟨9067914079732029642526745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6045276053154686428351163 9067914079732029642526745)
      ·
        refine ⟨6800935559799022231895059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9067914079732029642526745 6800935559799022231895059)
        ·
          refine ⟨10201403339698533347842589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6800935559799022231895059 10201403339698533347842589)
          ·
            refine ⟨3825526252386950005440971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10201403339698533347842589 3825526252386950005440971)
            ·
              refine ⟨5738289378580425008161457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3825526252386950005440971 5738289378580425008161457)
              ·
                refine ⟨4303717033935318756121093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5738289378580425008161457 4303717033935318756121093)
                ·
                  refine ⟨806946943862872266772705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4303717033935318756121093 806946943862872266772705)
                  ·
                    refine ⟨605210207897154200079529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 806946943862872266772705 605210207897154200079529)
                    ·
                      refine ⟨453907655922865650059647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 605210207897154200079529 453907655922865650059647)
                      ·
                        rfl

theorem cell23_883982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 4, 2, 2].length) (baseStart_883982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_883982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_883982 prefixEnd_883982 := by exact prefixLift 883982
  have htrace : WordTrace (prefixWord ++ tailWord_883982) baseStart_883982 baseEnd_883982 := by
    simpa [prefixWord, tailWord_883982, baseEnd_883982] using wordTrace_append hprefix tailTrace_883982
  have hstable : (prefixWord ++ tailWord_883982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883982).length < 2 ^ (prefixWord ++ tailWord_883982).sum := by decide
  have hdescent : baseEnd_883982 < baseStart_883982 := by decide
  rcases family_descends (prefixWord ++ tailWord_883982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884005 : List Nat := [1, 3, 1, 2, 4, 3, 1, 1, 7]
def baseStart_884005 : Nat := 118140960795 + 884005 * 2 ^ 59
def prefixEnd_884005 : Nat := 4983230072969 + 3 ^ 40 * 884005 * 2
def baseEnd_884005 : Nat := 50435496219768784452449

theorem tailTrace_884005 : CollatzResearch.WordTrace tailWord_884005 prefixEnd_884005 50435496219768784452449 := by
  unfold tailWord_884005
  simp only [CollatzResearch.WordTrace]
  refine ⟨32242311162408335879293469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21494874108272223919528979 32242311162408335879293469)
  ·
    refine ⟨12090866685903125954735051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32242311162408335879293469 12090866685903125954735051)
    ·
      refine ⟨18136300028854688932102577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12090866685903125954735051 18136300028854688932102577)
      ·
        refine ⟨13602225021641016699076933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18136300028854688932102577 13602225021641016699076933)
        ·
          refine ⟨2550417191557690631076925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13602225021641016699076933 2550417191557690631076925)
          ·
            refine ⟨956406446834133986653847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2550417191557690631076925 956406446834133986653847)
            ·
              refine ⟨1434609670251200979980771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 956406446834133986653847 1434609670251200979980771)
              ·
                refine ⟨2151914505376801469971157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1434609670251200979980771 2151914505376801469971157)
                ·
                  refine ⟨50435496219768784452449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2151914505376801469971157 50435496219768784452449)
                  ·
                    rfl

theorem cell23_884005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 1, 7].length) (baseStart_884005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_884005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_884005 prefixEnd_884005 := by exact prefixLift 884005
  have htrace : WordTrace (prefixWord ++ tailWord_884005) baseStart_884005 baseEnd_884005 := by
    simpa [prefixWord, tailWord_884005, baseEnd_884005] using wordTrace_append hprefix tailTrace_884005
  have hstable : (prefixWord ++ tailWord_884005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884005).length < 2 ^ (prefixWord ++ tailWord_884005).sum := by decide
  have hdescent : baseEnd_884005 < baseStart_884005 := by decide
  rcases family_descends (prefixWord ++ tailWord_884005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884055 : List Nat := [1, 1, 3, 2, 3, 2, 2, 2, 2, 1, 4]
def baseStart_884055 : Nat := 118140960795 + 884055 * 2 ^ 59
def prefixEnd_884055 : Nat := 4983230072969 + 3 ^ 40 * 884055 * 2
def baseEnd_884055 : Nat := 453945140010643864446811

theorem tailTrace_884055 : CollatzResearch.WordTrace tailWord_884055 prefixEnd_884055 453945140010643864446811 := by
  unfold tailWord_884055
  simp only [CollatzResearch.WordTrace]
  refine ⟨32244134812227194418613619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21496089874818129612409079 32244134812227194418613619)
  ·
    refine ⟨48366202218340791627920429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32244134812227194418613619 48366202218340791627920429)
    ·
      refine ⟨18137325831877796860470161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48366202218340791627920429 18137325831877796860470161)
      ·
        refine ⟨13602994373908347645352621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18137325831877796860470161 13602994373908347645352621)
        ·
          refine ⟨5101122890215630367007233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13602994373908347645352621 5101122890215630367007233)
          ·
            refine ⟨3825842167661722775255425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5101122890215630367007233 3825842167661722775255425)
            ·
              refine ⟨2869381625746292081441569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3825842167661722775255425 2869381625746292081441569)
              ·
                refine ⟨2152036219309719061081177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2869381625746292081441569 2152036219309719061081177)
                ·
                  refine ⟨1614027164482289295810883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2152036219309719061081177 1614027164482289295810883)
                  ·
                    refine ⟨2421040746723433943716325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1614027164482289295810883 2421040746723433943716325)
                    ·
                      refine ⟨453945140010643864446811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2421040746723433943716325 453945140010643864446811)
                      ·
                        rfl

theorem cell23_884055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 2, 2, 1, 4].length) (baseStart_884055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_884055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_884055 prefixEnd_884055 := by exact prefixLift 884055
  have htrace : WordTrace (prefixWord ++ tailWord_884055) baseStart_884055 baseEnd_884055 := by
    simpa [prefixWord, tailWord_884055, baseEnd_884055] using wordTrace_append hprefix tailTrace_884055
  have hstable : (prefixWord ++ tailWord_884055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884055).length < 2 ^ (prefixWord ++ tailWord_884055).sum := by decide
  have hdescent : baseEnd_884055 < baseStart_884055 := by decide
  rcases family_descends (prefixWord ++ tailWord_884055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884099 : List Nat := [1, 1, 1, 3, 5, 2, 2, 3, 1, 4]
def baseStart_884099 : Nat := 118140960795 + 884099 * 2 ^ 59
def prefixEnd_884099 : Nat := 4983230072969 + 3 ^ 40 * 884099 * 2
def baseEnd_884099 : Nat := 151322577719813897432203

theorem tailTrace_884099 : CollatzResearch.WordTrace tailWord_884099 prefixEnd_884099 151322577719813897432203 := by
  unfold tailWord_884099
  simp only [CollatzResearch.WordTrace]
  refine ⟨32245739624067789933215351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21497159749378526622143567 32245739624067789933215351)
  ·
    refine ⟨48368609436101684899823027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32245739624067789933215351 48368609436101684899823027)
    ·
      refine ⟨72552914154152527349734541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48368609436101684899823027 72552914154152527349734541)
      ·
        refine ⟨27207342807807197756150453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72552914154152527349734541 27207342807807197756150453)
        ·
          refine ⟨2550688388231924789639105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27207342807807197756150453 2550688388231924789639105)
          ·
            refine ⟨1913016291173943592229329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2550688388231924789639105 1913016291173943592229329)
            ·
              refine ⟨1434762218380457694171997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1913016291173943592229329 1434762218380457694171997)
              ·
                refine ⟨538035831892671635314499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1434762218380457694171997 538035831892671635314499)
                ·
                  refine ⟨807053747839007452971749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 538035831892671635314499 807053747839007452971749)
                  ·
                    refine ⟨151322577719813897432203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 807053747839007452971749 151322577719813897432203)
                    ·
                      rfl

theorem cell23_884099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 3, 1, 4].length) (baseStart_884099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_884099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_884099 prefixEnd_884099 := by exact prefixLift 884099
  have htrace : WordTrace (prefixWord ++ tailWord_884099) baseStart_884099 baseEnd_884099 := by
    simpa [prefixWord, tailWord_884099, baseEnd_884099] using wordTrace_append hprefix tailTrace_884099
  have hstable : (prefixWord ++ tailWord_884099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884099).length < 2 ^ (prefixWord ++ tailWord_884099).sum := by decide
  have hdescent : baseEnd_884099 < baseStart_884099 := by decide
  rcases family_descends (prefixWord ++ tailWord_884099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884172 : List Nat := [2, 2, 1, 4, 2, 1, 2, 1, 4, 4]
def baseStart_884172 : Nat := 118140960795 + 884172 * 2 ^ 59
def prefixEnd_884172 : Nat := 4983230072969 + 3 ^ 40 * 884172 * 2
def baseEnd_884172 : Nat := 151335072415739968894591

theorem tailTrace_884172 : CollatzResearch.WordTrace tailWord_884172 prefixEnd_884172 151335072415739968894591 := by
  unfold tailWord_884172
  simp only [CollatzResearch.WordTrace]
  refine ⟨16124201076401661700311385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21498934768535548933748513 16124201076401661700311385)
  ·
    refine ⟨12093150807301246275233539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16124201076401661700311385 12093150807301246275233539)
    ·
      refine ⟨18139726210951869412850309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12093150807301246275233539 18139726210951869412850309)
      ·
        refine ⟨3401198664553475514909433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18139726210951869412850309 3401198664553475514909433)
        ·
          refine ⟨2550898998415106636182075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3401198664553475514909433 2550898998415106636182075)
          ·
            refine ⟨3826348497622659954273113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2550898998415106636182075 3826348497622659954273113)
            ·
              refine ⟨2869761373216994965704835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3826348497622659954273113 2869761373216994965704835)
              ·
                refine ⟨4304642059825492448557253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2869761373216994965704835 4304642059825492448557253)
                ·
                  refine ⟨807120386217279834104485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4304642059825492448557253 807120386217279834104485)
                  ·
                    refine ⟨151335072415739968894591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 807120386217279834104485 151335072415739968894591)
                    ·
                      rfl

theorem cell23_884172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 4, 4].length) (baseStart_884172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_884172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_884172 prefixEnd_884172 := by exact prefixLift 884172
  have htrace : WordTrace (prefixWord ++ tailWord_884172) baseStart_884172 baseEnd_884172 := by
    simpa [prefixWord, tailWord_884172, baseEnd_884172] using wordTrace_append hprefix tailTrace_884172
  have hstable : (prefixWord ++ tailWord_884172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884172).length < 2 ^ (prefixWord ++ tailWord_884172).sum := by decide
  have hdescent : baseEnd_884172 < baseStart_884172 := by decide
  rcases family_descends (prefixWord ++ tailWord_884172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884185 : List Nat := [1, 2, 1, 2, 4, 3, 2, 8]
def baseStart_884185 : Nat := 118140960795 + 884185 * 2 ^ 59
def prefixEnd_884185 : Nat := 4983230072969 + 3 ^ 40 * 884185 * 2
def baseEnd_884185 : Nat := 16815255277619568734119

theorem tailTrace_884185 : CollatzResearch.WordTrace tailWord_884185 prefixEnd_884185 16815255277619568734119 := by
  unfold tailWord_884185
  simp only [CollatzResearch.WordTrace]
  refine ⟨32248876301756226620846009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21499250867837484413897339 32248876301756226620846009)
  ·
    refine ⟨24186657226317169965634507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32248876301756226620846009 24186657226317169965634507)
    ·
      refine ⟨36279985839475754948451761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24186657226317169965634507 36279985839475754948451761)
      ·
        refine ⟨27209989379606816211338821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36279985839475754948451761 27209989379606816211338821)
        ·
          refine ⟨5101873008676278039626029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27209989379606816211338821 5101873008676278039626029)
          ·
            refine ⟨1913202378253604264859761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5101873008676278039626029 1913202378253604264859761)
            ·
              refine ⟨1434901783690203198644821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1913202378253604264859761 1434901783690203198644821)
              ·
                refine ⟨16815255277619568734119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1434901783690203198644821 16815255277619568734119)
                ·
                  rfl

theorem cell23_884185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 8].length) (baseStart_884185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_884185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_884185 prefixEnd_884185 := by exact prefixLift 884185
  have htrace : WordTrace (prefixWord ++ tailWord_884185) baseStart_884185 baseEnd_884185 := by
    simpa [prefixWord, tailWord_884185, baseEnd_884185] using wordTrace_append hprefix tailTrace_884185
  have hstable : (prefixWord ++ tailWord_884185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884185).length < 2 ^ (prefixWord ++ tailWord_884185).sum := by decide
  have hdescent : baseEnd_884185 < baseStart_884185 := by decide
  rcases family_descends (prefixWord ++ tailWord_884185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884189 : List Nat := [1, 4, 3, 1, 1, 3, 1, 3, 2, 4]
def baseStart_884189 : Nat := 118140960795 + 884189 * 2 ^ 59
def prefixEnd_884189 : Nat := 4983230072969 + 3 ^ 40 * 884189 * 2
def baseEnd_884189 : Nat := 151337982139448780057065

theorem tailTrace_884189 : CollatzResearch.WordTrace tailWord_884189 prefixEnd_884189 151337982139448780057065 := by
  unfold tailWord_884189
  simp only [CollatzResearch.WordTrace]
  refine ⟨32249022193741735303991621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21499348129161156869327747 32249022193741735303991621)
  ·
    refine ⟨6046691661326575369498429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32249022193741735303991621 6046691661326575369498429)
    ·
      refine ⟨2267509372997465763561911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6046691661326575369498429 2267509372997465763561911)
      ·
        refine ⟨3401264059496198645342867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2267509372997465763561911 3401264059496198645342867)
        ·
          refine ⟨5101896089244297968014301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3401264059496198645342867 5101896089244297968014301)
          ·
            refine ⟨1913211033466611738005363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5101896089244297968014301 1913211033466611738005363)
            ·
              refine ⟨2869816550199917607008045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1913211033466611738005363 2869816550199917607008045)
              ·
                refine ⟨1076181206324969102628017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2869816550199917607008045 1076181206324969102628017)
                ·
                  refine ⟨807135904743726826971013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1076181206324969102628017 807135904743726826971013)
                  ·
                    refine ⟨151337982139448780057065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 807135904743726826971013 151337982139448780057065)
                    ·
                      rfl

theorem cell23_884189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_884189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_884189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_884189 prefixEnd_884189 := by exact prefixLift 884189
  have htrace : WordTrace (prefixWord ++ tailWord_884189) baseStart_884189 baseEnd_884189 := by
    simpa [prefixWord, tailWord_884189, baseEnd_884189] using wordTrace_append hprefix tailTrace_884189
  have hstable : (prefixWord ++ tailWord_884189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884189).length < 2 ^ (prefixWord ++ tailWord_884189).sum := by decide
  have hdescent : baseEnd_884189 < baseStart_884189 := by decide
  rcases family_descends (prefixWord ++ tailWord_884189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884199 : List Nat := [1, 1, 5, 2, 1, 2, 3, 2, 1, 2, 3]
def baseStart_884199 : Nat := 118140960795 + 884199 * 2 ^ 59
def prefixEnd_884199 : Nat := 4983230072969 + 3 ^ 40 * 884199 * 2
def baseEnd_884199 : Nat := 454019081224891301046149

theorem tailTrace_884199 : CollatzResearch.WordTrace tailWord_884199 prefixEnd_884199 454019081224891301046149 := by
  unfold tailWord_884199
  simp only [CollatzResearch.WordTrace]
  refine ⟨32249386923705507011855651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21499591282470338007903767 32249386923705507011855651)
  ·
    refine ⟨48374080385558260517783477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32249386923705507011855651 48374080385558260517783477)
    ·
      refine ⟨4535070036146086923542201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48374080385558260517783477 4535070036146086923542201)
      ·
        refine ⟨3401302527109565192656651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4535070036146086923542201 3401302527109565192656651)
        ·
          refine ⟨5101953790664347788984977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3401302527109565192656651 5101953790664347788984977)
          ·
            refine ⟨3826465342998260841738733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5101953790664347788984977 3826465342998260841738733)
            ·
              refine ⟨1434924503624347815652025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3826465342998260841738733 1434924503624347815652025)
              ·
                refine ⟨1076193377718260861739019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1434924503624347815652025 1076193377718260861739019)
                ·
                  refine ⟨1614290066577391292608529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1076193377718260861739019 1614290066577391292608529)
                  ·
                    refine ⟨1210717549933043469456397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1614290066577391292608529 1210717549933043469456397)
                    ·
                      refine ⟨454019081224891301046149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1210717549933043469456397 454019081224891301046149)
                      ·
                        rfl

theorem cell23_884199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_884199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_884199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_884199 prefixEnd_884199 := by exact prefixLift 884199
  have htrace : WordTrace (prefixWord ++ tailWord_884199) baseStart_884199 baseEnd_884199 := by
    simpa [prefixWord, tailWord_884199, baseEnd_884199] using wordTrace_append hprefix tailTrace_884199
  have hstable : (prefixWord ++ tailWord_884199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884199).length < 2 ^ (prefixWord ++ tailWord_884199).sum := by decide
  have hdescent : baseEnd_884199 < baseStart_884199 := by decide
  rcases family_descends (prefixWord ++ tailWord_884199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884245 : List Nat := [1, 3, 2, 1, 3, 2, 1, 1, 1, 8]
def baseStart_884245 : Nat := 118140960795 + 884245 * 2 ^ 59
def prefixEnd_884245 : Nat := 4983230072969 + 3 ^ 40 * 884245 * 2
def baseEnd_884245 : Nat := 151347567111666040356979

theorem tailTrace_884245 : CollatzResearch.WordTrace tailWord_884245 prefixEnd_884245 151347567111666040356979 := by
  unfold tailWord_884245
  simp only [CollatzResearch.WordTrace]
  refine ⟨32251064681538856868030189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21500709787692571245353459 32251064681538856868030189)
  ·
    refine ⟨12094149255577071325511321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32251064681538856868030189 12094149255577071325511321)
    ·
      refine ⟨9070611941682803494133491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12094149255577071325511321 9070611941682803494133491)
      ·
        refine ⟨13605917912524205241200237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9070611941682803494133491 13605917912524205241200237)
        ·
          refine ⟨5102219217196576965450089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13605917912524205241200237 5102219217196576965450089)
          ·
            refine ⟨3826664412897432724087567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5102219217196576965450089 3826664412897432724087567)
            ·
              refine ⟨5739996619346149086131351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3826664412897432724087567 5739996619346149086131351)
              ·
                refine ⟨8609994929019223629197027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5739996619346149086131351 8609994929019223629197027)
                ·
                  refine ⟨12914992393528835443795541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8609994929019223629197027 12914992393528835443795541)
                  ·
                    refine ⟨151347567111666040356979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 12914992393528835443795541 151347567111666040356979)
                    ·
                      rfl

theorem cell23_884245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 8].length) (baseStart_884245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_884245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_884245 prefixEnd_884245 := by exact prefixLift 884245
  have htrace : WordTrace (prefixWord ++ tailWord_884245) baseStart_884245 baseEnd_884245 := by
    simpa [prefixWord, tailWord_884245, baseEnd_884245] using wordTrace_append hprefix tailTrace_884245
  have hstable : (prefixWord ++ tailWord_884245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884245).length < 2 ^ (prefixWord ++ tailWord_884245).sum := by decide
  have hdescent : baseEnd_884245 < baseStart_884245 := by decide
  rcases family_descends (prefixWord ++ tailWord_884245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884255 : List Nat := [1, 1, 2, 4, 1, 1, 2, 1, 4, 1, 5]
def baseStart_884255 : Nat := 118140960795 + 884255 * 2 ^ 59
def prefixEnd_884255 : Nat := 4983230072969 + 3 ^ 40 * 884255 * 2
def baseEnd_884255 : Nat := 454047836141543081945891

theorem tailTrace_884255 : CollatzResearch.WordTrace tailWord_884255 prefixEnd_884255 454047836141543081945891 := by
  unfold tailWord_884255
  simp only [CollatzResearch.WordTrace]
  refine ⟨32251429411502628575894219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21500952941001752383929479 32251429411502628575894219)
  ·
    refine ⟨48377144117253942863841329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32251429411502628575894219 48377144117253942863841329)
    ·
      refine ⟨36282858087940457147880997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48377144117253942863841329 36282858087940457147880997)
      ·
        refine ⟨6803035891488835715227687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36282858087940457147880997 6803035891488835715227687)
        ·
          refine ⟨10204553837233253572841531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6803035891488835715227687 10204553837233253572841531)
          ·
            refine ⟨15306830755849880359262297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10204553837233253572841531 15306830755849880359262297)
            ·
              refine ⟨11480123066887410269446723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15306830755849880359262297 11480123066887410269446723)
              ·
                refine ⟨17220184600331115404170085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11480123066887410269446723 17220184600331115404170085)
                ·
                  refine ⟨3228784612562084138281891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17220184600331115404170085 3228784612562084138281891)
                  ·
                    refine ⟨4843176918843126207422837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3228784612562084138281891 4843176918843126207422837)
                    ·
                      refine ⟨454047836141543081945891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4843176918843126207422837 454047836141543081945891)
                      ·
                        rfl

theorem cell23_884255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_884255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_884255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_884255 prefixEnd_884255 := by exact prefixLift 884255
  have htrace : WordTrace (prefixWord ++ tailWord_884255) baseStart_884255 baseEnd_884255 := by
    simpa [prefixWord, tailWord_884255, baseEnd_884255] using wordTrace_append hprefix tailTrace_884255
  have hstable : (prefixWord ++ tailWord_884255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884255).length < 2 ^ (prefixWord ++ tailWord_884255).sum := by decide
  have hdescent : baseEnd_884255 < baseStart_884255 := by decide
  rcases family_descends (prefixWord ++ tailWord_884255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884305 : List Nat := [1, 2, 2, 1, 3, 2, 1, 1, 3, 7]
def baseStart_884305 : Nat := 118140960795 + 884305 * 2 ^ 59
def prefixEnd_884305 : Nat := 4983230072969 + 3 ^ 40 * 884305 * 2
def baseEnd_884305 : Nat := 151357836724755962106887

theorem tailTrace_884305 : CollatzResearch.WordTrace tailWord_884305 prefixEnd_884305 151357836724755962106887 := by
  unfold tailWord_884305
  simp only [CollatzResearch.WordTrace]
  refine ⟨32253253061321487115214369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21502168707547658076809579 32253253061321487115214369)
  ·
    refine ⟨24189939795991115336410777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32253253061321487115214369 24189939795991115336410777)
    ·
      refine ⟨18142454846993336502308083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24189939795991115336410777 18142454846993336502308083)
      ·
        refine ⟨27213682270490004753462125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18142454846993336502308083 27213682270490004753462125)
        ·
          refine ⟨10205130851433751782548297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27213682270490004753462125 10205130851433751782548297)
          ·
            refine ⟨7653848138575313836911223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10205130851433751782548297 7653848138575313836911223)
            ·
              refine ⟨11480772207862970755366835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7653848138575313836911223 11480772207862970755366835)
              ·
                refine ⟨17221158311794456133050253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11480772207862970755366835 17221158311794456133050253)
                ·
                  refine ⟨6457934366922921049893845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17221158311794456133050253 6457934366922921049893845)
                  ·
                    refine ⟨151357836724755962106887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6457934366922921049893845 151357836724755962106887)
                    ·
                      rfl

theorem cell23_884305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 7].length) (baseStart_884305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_884305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_884305 prefixEnd_884305 := by exact prefixLift 884305
  have htrace : WordTrace (prefixWord ++ tailWord_884305) baseStart_884305 baseEnd_884305 := by
    simpa [prefixWord, tailWord_884305, baseEnd_884305] using wordTrace_append hprefix tailTrace_884305
  have hstable : (prefixWord ++ tailWord_884305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884305).length < 2 ^ (prefixWord ++ tailWord_884305).sum := by decide
  have hdescent : baseEnd_884305 < baseStart_884305 := by decide
  rcases family_descends (prefixWord ++ tailWord_884305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884479 : List Nat := [1, 1, 2, 2, 1, 3, 5, 1, 1, 2, 4]
def baseStart_884479 : Nat := 118140960795 + 884479 * 2 ^ 59
def prefixEnd_884479 : Nat := 4983230072969 + 3 ^ 40 * 884479 * 2
def baseEnd_884479 : Nat := 454162855808150205544861

theorem tailTrace_884479 : CollatzResearch.WordTrace tailWord_884479 prefixEnd_884479 454162855808150205544861 := by
  unfold tailWord_884479
  simp only [CollatzResearch.WordTrace]
  refine ⟨32259599362691114832048491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21506399575127409888032327 32259599362691114832048491)
  ·
    refine ⟨48389399044036672248072737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32259599362691114832048491 48389399044036672248072737)
    ·
      refine ⟨36292049283027504186054553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48389399044036672248072737 36292049283027504186054553)
      ·
        refine ⟨27219036962270628139540915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36292049283027504186054553 27219036962270628139540915)
        ·
          refine ⟨40828555443405942209311373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27219036962270628139540915 40828555443405942209311373)
          ·
            refine ⟨15310708291277228328491765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40828555443405942209311373 15310708291277228328491765)
            ·
              refine ⟨1435378902307240155796103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15310708291277228328491765 1435378902307240155796103)
              ·
                refine ⟨2153068353460860233694155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1435378902307240155796103 2153068353460860233694155)
                ·
                  refine ⟨3229602530191290350541233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2153068353460860233694155 3229602530191290350541233)
                  ·
                    refine ⟨2422201897643467762905925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3229602530191290350541233 2422201897643467762905925)
                    ·
                      refine ⟨454162855808150205544861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2422201897643467762905925 454162855808150205544861)
                      ·
                        rfl

theorem cell23_884479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 1, 1, 2, 4].length) (baseStart_884479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_884479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_884479 prefixEnd_884479 := by exact prefixLift 884479
  have htrace : WordTrace (prefixWord ++ tailWord_884479) baseStart_884479 baseEnd_884479 := by
    simpa [prefixWord, tailWord_884479, baseEnd_884479] using wordTrace_append hprefix tailTrace_884479
  have hstable : (prefixWord ++ tailWord_884479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884479).length < 2 ^ (prefixWord ++ tailWord_884479).sum := by decide
  have hdescent : baseEnd_884479 < baseStart_884479 := by decide
  rcases family_descends (prefixWord ++ tailWord_884479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884517 : List Nat := [1, 3, 1, 2, 3, 3, 3, 2, 1, 2, 2]
def baseStart_884517 : Nat := 118140960795 + 884517 * 2 ^ 59
def prefixEnd_884517 : Nat := 4983230072969 + 3 ^ 40 * 884517 * 2
def baseEnd_884517 : Nat := 454182368073021056869687

theorem tailTrace_884517 : CollatzResearch.WordTrace tailWord_884517 prefixEnd_884517 454182368073021056869687 := by
  unfold tailWord_884517
  simp only [CollatzResearch.WordTrace]
  refine ⟨32260985336553447321931805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21507323557702298214621203 32260985336553447321931805)
  ·
    refine ⟨12097869501207542745724427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32260985336553447321931805 12097869501207542745724427)
    ·
      refine ⟨18146804251811314118586641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12097869501207542745724427 18146804251811314118586641)
      ·
        refine ⟨13610103188858485588939981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18146804251811314118586641 13610103188858485588939981)
        ·
          refine ⟨5103788695821932095852493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13610103188858485588939981 5103788695821932095852493)
          ·
            refine ⟨1913920760933224535944685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5103788695821932095852493 1913920760933224535944685)
            ·
              refine ⟨717720285349959200979257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1913920760933224535944685 717720285349959200979257)
              ·
                refine ⟨538290214012469400734443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 717720285349959200979257 538290214012469400734443)
                ·
                  refine ⟨807435321018704101101665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 538290214012469400734443 807435321018704101101665)
                  ·
                    refine ⟨605576490764028075826249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 807435321018704101101665 605576490764028075826249)
                    ·
                      refine ⟨454182368073021056869687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 605576490764028075826249 454182368073021056869687)
                      ·
                        rfl

theorem cell23_884517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 3, 2, 1, 2, 2].length) (baseStart_884517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_884517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_884517 prefixEnd_884517 := by exact prefixLift 884517
  have htrace : WordTrace (prefixWord ++ tailWord_884517) baseStart_884517 baseEnd_884517 := by
    simpa [prefixWord, tailWord_884517, baseEnd_884517] using wordTrace_append hprefix tailTrace_884517
  have hstable : (prefixWord ++ tailWord_884517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884517).length < 2 ^ (prefixWord ++ tailWord_884517).sum := by decide
  have hdescent : baseEnd_884517 < baseStart_884517 := by decide
  rcases family_descends (prefixWord ++ tailWord_884517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884537 : List Nat := [1, 2, 1, 7, 2, 1, 1, 2, 1, 2, 3]
def baseStart_884537 : Nat := 118140960795 + 884537 * 2 ^ 59
def prefixEnd_884537 : Nat := 4983230072969 + 3 ^ 40 * 884537 * 2
def baseEnd_884537 : Nat := 454192637686110978619595

theorem tailTrace_884537 : CollatzResearch.WordTrace tailWord_884537 prefixEnd_884537 454192637686110978619595 := by
  unfold tailWord_884537
  simp only [CollatzResearch.WordTrace]
  refine ⟨32261714796480990737659865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21507809864320660491773243 32261714796480990737659865)
  ·
    refine ⟨24196286097360743053244899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32261714796480990737659865 24196286097360743053244899)
    ·
      refine ⟨36294429146041114579867349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24196286097360743053244899 36294429146041114579867349)
      ·
        refine ⟨850650683110338622965641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 36294429146041114579867349 850650683110338622965641)
        ·
          refine ⟨637988012332753967224231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 850650683110338622965641 637988012332753967224231)
          ·
            refine ⟨956982018499130950836347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 637988012332753967224231 956982018499130950836347)
            ·
              refine ⟨1435473027748696426254521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 956982018499130950836347 1435473027748696426254521)
              ·
                refine ⟨1076604770811522319690891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1435473027748696426254521 1076604770811522319690891)
                ·
                  refine ⟨1614907156217283479536337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1076604770811522319690891 1614907156217283479536337)
                  ·
                    refine ⟨1211180367162962609652253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1614907156217283479536337 1211180367162962609652253)
                    ·
                      refine ⟨454192637686110978619595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1211180367162962609652253 454192637686110978619595)
                      ·
                        rfl

theorem cell23_884537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_884537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_884537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_884537 prefixEnd_884537 := by exact prefixLift 884537
  have htrace : WordTrace (prefixWord ++ tailWord_884537) baseStart_884537 baseEnd_884537 := by
    simpa [prefixWord, tailWord_884537, baseEnd_884537] using wordTrace_append hprefix tailTrace_884537
  have hstable : (prefixWord ++ tailWord_884537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884537).length < 2 ^ (prefixWord ++ tailWord_884537).sum := by decide
  have hdescent : baseEnd_884537 < baseStart_884537 := by decide
  rcases family_descends (prefixWord ++ tailWord_884537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884543 : List Nat := [1, 1, 2, 2, 6, 1, 1, 1, 3, 3, 2]
def baseStart_884543 : Nat := 118140960795 + 884543 * 2 ^ 59
def prefixEnd_884543 : Nat := 4983230072969 + 3 ^ 40 * 884543 * 2
def baseEnd_884543 : Nat := 454195718570037955144567

theorem tailTrace_884543 : CollatzResearch.WordTrace tailWord_884543 prefixEnd_884543 454195718570037955144567 := by
  unfold tailWord_884543
  simp only [CollatzResearch.WordTrace]
  refine ⟨32261933634459253762378283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21507955756306169174918855 32261933634459253762378283)
  ·
    refine ⟨48392900451688880643567425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32261933634459253762378283 48392900451688880643567425)
    ·
      refine ⟨36294675338766660482675569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48392900451688880643567425 36294675338766660482675569)
      ·
        refine ⟨27221006504074995362006677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36294675338766660482675569 27221006504074995362006677)
        ·
          refine ⟨1275984679878515407594063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 27221006504074995362006677 1275984679878515407594063)
          ·
            refine ⟨1913977019817773111391095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1275984679878515407594063 1913977019817773111391095)
            ·
              refine ⟨2870965529726659667086643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1913977019817773111391095 2870965529726659667086643)
              ·
                refine ⟨4306448294589989500629965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2870965529726659667086643 4306448294589989500629965)
                ·
                  refine ⟨1614918110471246062736237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4306448294589989500629965 1614918110471246062736237)
                  ·
                    refine ⟨605594291426717273526089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1614918110471246062736237 605594291426717273526089)
                    ·
                      refine ⟨454195718570037955144567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 605594291426717273526089 454195718570037955144567)
                      ·
                        rfl

theorem cell23_884543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 3, 3, 2].length) (baseStart_884543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_884543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_884543 prefixEnd_884543 := by exact prefixLift 884543
  have htrace : WordTrace (prefixWord ++ tailWord_884543) baseStart_884543 baseEnd_884543 := by
    simpa [prefixWord, tailWord_884543, baseEnd_884543] using wordTrace_append hprefix tailTrace_884543
  have hstable : (prefixWord ++ tailWord_884543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884543).length < 2 ^ (prefixWord ++ tailWord_884543).sum := by decide
  have hdescent : baseEnd_884543 < baseStart_884543 := by decide
  rcases family_descends (prefixWord ++ tailWord_884543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884550 : List Nat := [6, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3]
def baseStart_884550 : Nat := 118140960795 + 884550 * 2 ^ 59
def prefixEnd_884550 : Nat := 4983230072969 + 3 ^ 40 * 884550 * 2
def baseEnd_884550 : Nat := 454199312934619427757035

theorem tailTrace_884550 : CollatzResearch.WordTrace tailWord_884550 prefixEnd_884550 454199312934619427757035 := by
  unfold tailWord_884550
  simp only [CollatzResearch.WordTrace]
  refine ⟨1008193404544809186183847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21508125963622595971922069 1008193404544809186183847)
  ·
    refine ⟨1512290106817213779275771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1008193404544809186183847 1512290106817213779275771)
    ·
      refine ⟨2268435160225820668913657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1512290106817213779275771 2268435160225820668913657)
      ·
        refine ⟨1701326370169365501685243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2268435160225820668913657 1701326370169365501685243)
        ·
          refine ⟨2551989555254048252527865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1701326370169365501685243 2551989555254048252527865)
          ·
            refine ⟨1913992166440536189395899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2551989555254048252527865 1913992166440536189395899)
            ·
              refine ⟨2870988249660804284093849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1913992166440536189395899 2870988249660804284093849)
              ·
                refine ⟨2153241187245603213070387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2870988249660804284093849 2153241187245603213070387)
                ·
                  refine ⟨3229861780868404819605581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2153241187245603213070387 3229861780868404819605581)
                  ·
                    refine ⟨1211198167825651807352093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3229861780868404819605581 1211198167825651807352093)
                    ·
                      refine ⟨454199312934619427757035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1211198167825651807352093 454199312934619427757035)
                      ·
                        rfl

theorem cell23_884550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_884550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_884550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_884550 prefixEnd_884550 := by exact prefixLift 884550
  have htrace : WordTrace (prefixWord ++ tailWord_884550) baseStart_884550 baseEnd_884550 := by
    simpa [prefixWord, tailWord_884550, baseEnd_884550] using wordTrace_append hprefix tailTrace_884550
  have hstable : (prefixWord ++ tailWord_884550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884550).length < 2 ^ (prefixWord ++ tailWord_884550).sum := by decide
  have hdescent : baseEnd_884550 < baseStart_884550 := by decide
  rcases family_descends (prefixWord ++ tailWord_884550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884569 : List Nat := [1, 2, 1, 2, 2, 3, 2, 2, 2, 2, 4]
def baseStart_884569 : Nat := 118140960795 + 884569 * 2 ^ 59
def prefixEnd_884569 : Nat := 4983230072969 + 3 ^ 40 * 884569 * 2
def baseEnd_884569 : Nat := 454209069067054853419447

theorem tailTrace_884569 : CollatzResearch.WordTrace tailWord_884569 prefixEnd_884569 454209069067054853419447 := by
  unfold tailWord_884569
  simp only [CollatzResearch.WordTrace]
  refine ⟨32262881932365060202824761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21508587954910040135216507 32262881932365060202824761)
  ·
    refine ⟨24197161449273795152118571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32262881932365060202824761 24197161449273795152118571)
    ·
      refine ⟨36295742173910692728177857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24197161449273795152118571 36295742173910692728177857)
      ·
        refine ⟨27221806630433019546133393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36295742173910692728177857 27221806630433019546133393)
        ·
          refine ⟨20416354972824764659600045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27221806630433019546133393 20416354972824764659600045)
          ·
            refine ⟨7656133114809286747350017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20416354972824764659600045 7656133114809286747350017)
            ·
              refine ⟨5742099836106965060512513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7656133114809286747350017 5742099836106965060512513)
              ·
                refine ⟨4306574877080223795384385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5742099836106965060512513 4306574877080223795384385)
                ·
                  refine ⟨3229931157810167846538289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4306574877080223795384385 3229931157810167846538289)
                  ·
                    refine ⟨2422448368357625884903717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3229931157810167846538289 2422448368357625884903717)
                    ·
                      refine ⟨454209069067054853419447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2422448368357625884903717 454209069067054853419447)
                      ·
                        rfl

theorem cell23_884569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2, 2, 4].length) (baseStart_884569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_884569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_884569 prefixEnd_884569 := by exact prefixLift 884569
  have htrace : WordTrace (prefixWord ++ tailWord_884569) baseStart_884569 baseEnd_884569 := by
    simpa [prefixWord, tailWord_884569, baseEnd_884569] using wordTrace_append hprefix tailTrace_884569
  have hstable : (prefixWord ++ tailWord_884569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884569).length < 2 ^ (prefixWord ++ tailWord_884569).sum := by decide
  have hdescent : baseEnd_884569 < baseStart_884569 := by decide
  rcases family_descends (prefixWord ++ tailWord_884569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884590 : List Nat := [4, 1, 2, 3, 1, 2, 2, 1, 1, 4, 2]
def baseStart_884590 : Nat := 118140960795 + 884590 * 2 ^ 59
def prefixEnd_884590 : Nat := 4983230072969 + 3 ^ 40 * 884590 * 2
def baseEnd_884590 : Nat := 454219852160799271256851

theorem tailTrace_884590 : CollatzResearch.WordTrace tailWord_884590 prefixEnd_884590 454219852160799271256851 := by
  unfold tailWord_884590
  simp only [CollatzResearch.WordTrace]
  refine ⟨4032955983161122598667403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21509098576859320526226149 4032955983161122598667403)
  ·
    refine ⟨6049433974741683898001105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4032955983161122598667403 6049433974741683898001105)
    ·
      refine ⟨4537075481056262923500829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6049433974741683898001105 4537075481056262923500829)
      ·
        refine ⟨1701403305396098596312811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4537075481056262923500829 1701403305396098596312811)
        ·
          refine ⟨2552104958094147894469217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1701403305396098596312811 2552104958094147894469217)
          ·
            refine ⟨1914078718570610920851913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2552104958094147894469217 1914078718570610920851913)
            ·
              refine ⟨1435559038927958190638935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1914078718570610920851913 1435559038927958190638935)
              ·
                refine ⟨2153338558391937285958403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1435559038927958190638935 2153338558391937285958403)
                ·
                  refine ⟨3230007837587905928937605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2153338558391937285958403 3230007837587905928937605)
                  ·
                    refine ⟨605626469547732361675801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3230007837587905928937605 605626469547732361675801)
                    ·
                      refine ⟨454219852160799271256851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 605626469547732361675801 454219852160799271256851)
                      ·
                        rfl

theorem cell23_884590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_884590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_884590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_884590 prefixEnd_884590 := by exact prefixLift 884590
  have htrace : WordTrace (prefixWord ++ tailWord_884590) baseStart_884590 baseEnd_884590 := by
    simpa [prefixWord, tailWord_884590, baseEnd_884590] using wordTrace_append hprefix tailTrace_884590
  have hstable : (prefixWord ++ tailWord_884590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884590).length < 2 ^ (prefixWord ++ tailWord_884590).sum := by decide
  have hdescent : baseEnd_884590 < baseStart_884590 := by decide
  rcases family_descends (prefixWord ++ tailWord_884590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884659 : List Nat := [1, 1, 1, 2, 3, 1, 3, 1, 2, 4, 4]
def baseStart_884659 : Nat := 118140960795 + 884659 * 2 ^ 59
def prefixEnd_884659 : Nat := 4983230072969 + 3 ^ 40 * 884659 * 2
def baseEnd_884659 : Nat := 454255282325959501294033

theorem tailTrace_884659 : CollatzResearch.WordTrace tailWord_884659 prefixEnd_884659 454255282325959501294033 := by
  unfold tailWord_884659
  simp only [CollatzResearch.WordTrace]
  refine ⟨32266164502039005573601031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21510776334692670382400687 32266164502039005573601031)
  ·
    refine ⟨48399246753058508360401547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32266164502039005573601031 48399246753058508360401547)
    ·
      refine ⟨72598870129587762540602321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48399246753058508360401547 72598870129587762540602321)
      ·
        refine ⟨54449152597190821905451741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72598870129587762540602321 54449152597190821905451741)
        ·
          refine ⟨20418432223946558214544403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54449152597190821905451741 20418432223946558214544403)
          ·
            refine ⟨30627648335919837321816605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20418432223946558214544403 30627648335919837321816605)
            ·
              refine ⟨11485368125969938995681227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30627648335919837321816605 11485368125969938995681227)
              ·
                refine ⟨17228052188954908493521841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11485368125969938995681227 17228052188954908493521841)
                ·
                  refine ⟨12921039141716181370141381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17228052188954908493521841 12921039141716181370141381)
                  ·
                    refine ⟨2422694839071784006901509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12921039141716181370141381 2422694839071784006901509)
                    ·
                      refine ⟨454255282325959501294033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2422694839071784006901509 454255282325959501294033)
                      ·
                        rfl

theorem cell23_884659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 4, 4].length) (baseStart_884659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_884659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_884659 prefixEnd_884659 := by exact prefixLift 884659
  have htrace : WordTrace (prefixWord ++ tailWord_884659) baseStart_884659 baseEnd_884659 := by
    simpa [prefixWord, tailWord_884659, baseEnd_884659] using wordTrace_append hprefix tailTrace_884659
  have hstable : (prefixWord ++ tailWord_884659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884659).length < 2 ^ (prefixWord ++ tailWord_884659).sum := by decide
  have hdescent : baseEnd_884659 < baseStart_884659 := by decide
  rcases family_descends (prefixWord ++ tailWord_884659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884686 : List Nat := [4, 1, 1, 1, 2, 2, 2, 4, 6]
def baseStart_884686 : Nat := 118140960795 + 884686 * 2 ^ 59
def prefixEnd_884686 : Nat := 4983230072969 + 3 ^ 40 * 884686 * 2
def baseEnd_884686 : Nat := 50474349589292321739601

theorem tailTrace_884686 : CollatzResearch.WordTrace tailWord_884686 prefixEnd_884686 50474349589292321739601 := by
  unfold tailWord_884686
  simp only [CollatzResearch.WordTrace]
  refine ⟨4033393659117648648104239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21511432848627459456555941 4033393659117648648104239)
  ·
    refine ⟨6050090488676472972156359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4033393659117648648104239 6050090488676472972156359)
    ·
      refine ⟨9075135733014709458234539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6050090488676472972156359 9075135733014709458234539)
      ·
        refine ⟨13612703599522064187351809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9075135733014709458234539 13612703599522064187351809)
        ·
          refine ⟨10209527699641548140513857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13612703599522064187351809 10209527699641548140513857)
          ·
            refine ⟨7657145774731161105385393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10209527699641548140513857 7657145774731161105385393)
            ·
              refine ⟨5742859331048370829039045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7657145774731161105385393 5742859331048370829039045)
              ·
                refine ⟨1076786124571569530444821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5742859331048370829039045 1076786124571569530444821)
                ·
                  refine ⟨50474349589292321739601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1076786124571569530444821 50474349589292321739601)
                  ·
                    rfl

theorem cell23_884686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 4, 6].length) (baseStart_884686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_884686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_884686 prefixEnd_884686 := by exact prefixLift 884686
  have htrace : WordTrace (prefixWord ++ tailWord_884686) baseStart_884686 baseEnd_884686 := by
    simpa [prefixWord, tailWord_884686, baseEnd_884686] using wordTrace_append hprefix tailTrace_884686
  have hstable : (prefixWord ++ tailWord_884686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884686).length < 2 ^ (prefixWord ++ tailWord_884686).sum := by decide
  have hdescent : baseEnd_884686 < baseStart_884686 := by decide
  rcases family_descends (prefixWord ++ tailWord_884686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884689 : List Nat := [1, 2, 2, 1, 2, 1, 2, 3, 1, 2, 6]
def baseStart_884689 : Nat := 118140960795 + 884689 * 2 ^ 59
def prefixEnd_884689 : Nat := 4983230072969 + 3 ^ 40 * 884689 * 2
def baseEnd_884689 : Nat := 454270686745594383918895

theorem tailTrace_884689 : CollatzResearch.WordTrace tailWord_884689 prefixEnd_884689 454270686745594383918895 := by
  unfold tailWord_884689
  simp only [CollatzResearch.WordTrace]
  refine ⟨32267258691930320697193121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21511505794620213798128747 32267258691930320697193121)
  ·
    refine ⟨24200444018947740522894841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32267258691930320697193121 24200444018947740522894841)
    ·
      refine ⟨18150333014210805392171131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24200444018947740522894841 18150333014210805392171131)
      ·
        refine ⟨27225499521316208088256697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18150333014210805392171131 27225499521316208088256697)
        ·
          refine ⟨20419124640987156066192523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27225499521316208088256697 20419124640987156066192523)
          ·
            refine ⟨30628686961480734099288785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20419124640987156066192523 30628686961480734099288785)
            ·
              refine ⟨22971515221110550574466589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30628686961480734099288785 22971515221110550574466589)
              ·
                refine ⟨8614318207916456465424971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22971515221110550574466589 8614318207916456465424971)
                ·
                  refine ⟨12921477311874684698137457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8614318207916456465424971 12921477311874684698137457)
                  ·
                    refine ⟨9691107983906013523603093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12921477311874684698137457 9691107983906013523603093)
                    ·
                      refine ⟨454270686745594383918895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9691107983906013523603093 454270686745594383918895)
                      ·
                        rfl

theorem cell23_884689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 2, 6].length) (baseStart_884689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_884689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_884689 prefixEnd_884689 := by exact prefixLift 884689
  have htrace : WordTrace (prefixWord ++ tailWord_884689) baseStart_884689 baseEnd_884689 := by
    simpa [prefixWord, tailWord_884689, baseEnd_884689] using wordTrace_append hprefix tailTrace_884689
  have hstable : (prefixWord ++ tailWord_884689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884689).length < 2 ^ (prefixWord ++ tailWord_884689).sum := by decide
  have hdescent : baseEnd_884689 < baseStart_884689 := by decide
  rcases family_descends (prefixWord ++ tailWord_884689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884703 : List Nat := [1, 1, 2, 3, 4, 1, 4, 1, 6]
def baseStart_884703 : Nat := 118140960795 + 884703 * 2 ^ 59
def prefixEnd_884703 : Nat := 4983230072969 + 3 ^ 40 * 884703 * 2
def baseEnd_884703 : Nat := 50475319497195258793759

theorem tailTrace_884703 : CollatzResearch.WordTrace tailWord_884703 prefixEnd_884703 50475319497195258793759 := by
  unfold tailWord_884703
  simp only [CollatzResearch.WordTrace]
  refine ⟨32267769313879601088202763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21511846209253067392135175 32267769313879601088202763)
  ·
    refine ⟨48401653970819401632304145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32267769313879601088202763 48401653970819401632304145)
    ·
      refine ⟨36301240478114551224228109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48401653970819401632304145 36301240478114551224228109)
      ·
        refine ⟨13612965179292956709085541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36301240478114551224228109 13612965179292956709085541)
        ·
          refine ⟨2552430971117429382953539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13612965179292956709085541 2552430971117429382953539)
          ·
            refine ⟨3828646456676144074430309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2552430971117429382953539 3828646456676144074430309)
            ·
              refine ⟨717871210626777013955683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3828646456676144074430309 717871210626777013955683)
              ·
                refine ⟨1076806815940165520933525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 717871210626777013955683 1076806815940165520933525)
                ·
                  refine ⟨50475319497195258793759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1076806815940165520933525 50475319497195258793759)
                  ·
                    rfl

theorem cell23_884703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 4, 1, 6].length) (baseStart_884703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_884703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_884703 prefixEnd_884703 := by exact prefixLift 884703
  have htrace : WordTrace (prefixWord ++ tailWord_884703) baseStart_884703 baseEnd_884703 := by
    simpa [prefixWord, tailWord_884703, baseEnd_884703] using wordTrace_append hprefix tailTrace_884703
  have hstable : (prefixWord ++ tailWord_884703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884703).length < 2 ^ (prefixWord ++ tailWord_884703).sum := by decide
  have hdescent : baseEnd_884703 < baseStart_884703 := by decide
  rcases family_descends (prefixWord ++ tailWord_884703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884717 : List Nat := [1, 5, 1, 4, 1, 1, 2, 1, 2, 2, 3]
def baseStart_884717 : Nat := 118140960795 + 884717 * 2 ^ 59
def prefixEnd_884717 : Nat := 4983230072969 + 3 ^ 40 * 884717 * 2
def baseEnd_884717 : Nat := 454285064203920274368767

theorem tailTrace_884717 : CollatzResearch.WordTrace tailWord_884717 prefixEnd_884717 454285064203920274368767 := by
  unfold tailWord_884717
  simp only [CollatzResearch.WordTrace]
  refine ⟨32268279935828881479212405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21512186623885920986141603 32268279935828881479212405)
  ·
    refine ⟨3025151243983957638676163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32268279935828881479212405 3025151243983957638676163)
    ·
      refine ⟨4537726865975936458014245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3025151243983957638676163 4537726865975936458014245)
      ·
        refine ⟨850823787370488085877671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4537726865975936458014245 850823787370488085877671)
        ·
          refine ⟨1276235681055732128816507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 850823787370488085877671 1276235681055732128816507)
          ·
            refine ⟨1914353521583598193224761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1276235681055732128816507 1914353521583598193224761)
            ·
              refine ⟨1435765141187698644918571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1914353521583598193224761 1435765141187698644918571)
              ·
                refine ⟨2153647711781547967377857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1435765141187698644918571 2153647711781547967377857)
                ·
                  refine ⟨1615235783836160975533393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2153647711781547967377857 1615235783836160975533393)
                  ·
                    refine ⟨1211426837877120731650045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1615235783836160975533393 1211426837877120731650045)
                    ·
                      refine ⟨454285064203920274368767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1211426837877120731650045 454285064203920274368767)
                      ·
                        rfl

theorem cell23_884717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_884717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_884717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_884717 prefixEnd_884717 := by exact prefixLift 884717
  have htrace : WordTrace (prefixWord ++ tailWord_884717) baseStart_884717 baseEnd_884717 := by
    simpa [prefixWord, tailWord_884717, baseEnd_884717] using wordTrace_append hprefix tailTrace_884717
  have hstable : (prefixWord ++ tailWord_884717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884717).length < 2 ^ (prefixWord ++ tailWord_884717).sum := by decide
  have hdescent : baseEnd_884717 < baseStart_884717 := by decide
  rcases family_descends (prefixWord ++ tailWord_884717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884773 : List Nat := [1, 3, 1, 2, 2, 3, 2, 1, 3, 2, 3]
def baseStart_884773 : Nat := 118140960795 + 884773 * 2 ^ 59
def prefixEnd_884773 : Nat := 4983230072969 + 3 ^ 40 * 884773 * 2
def baseEnd_884773 : Nat := 454313819120572055268509

theorem tailTrace_884773 : CollatzResearch.WordTrace tailWord_884773 prefixEnd_884773 454313819120572055268509 := by
  unfold tailWord_884773
  simp only [CollatzResearch.WordTrace]
  refine ⟨32270322423626003043250973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21513548282417335362167315 32270322423626003043250973)
  ·
    refine ⟨12101370908859751141219115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32270322423626003043250973 12101370908859751141219115)
    ·
      refine ⟨18152056363289626711828673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12101370908859751141219115 18152056363289626711828673)
      ·
        refine ⟨13614042272467220033871505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18152056363289626711828673 13614042272467220033871505)
        ·
          refine ⟨10210531704350415025403629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13614042272467220033871505 10210531704350415025403629)
          ·
            refine ⟨3828949389131405634526361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10210531704350415025403629 3828949389131405634526361)
            ·
              refine ⟨2871712041848554225894771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3828949389131405634526361 2871712041848554225894771)
              ·
                refine ⟨4307568062772831338842157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2871712041848554225894771 4307568062772831338842157)
                ·
                  refine ⟨1615338023539811752065809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4307568062772831338842157 1615338023539811752065809)
                  ·
                    refine ⟨1211503517654858814049357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1615338023539811752065809 1211503517654858814049357)
                    ·
                      refine ⟨454313819120572055268509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1211503517654858814049357 454313819120572055268509)
                      ·
                        rfl

theorem cell23_884773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 3, 2, 3].length) (baseStart_884773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_884773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_884773 prefixEnd_884773 := by exact prefixLift 884773
  have htrace : WordTrace (prefixWord ++ tailWord_884773) baseStart_884773 baseEnd_884773 := by
    simpa [prefixWord, tailWord_884773, baseEnd_884773] using wordTrace_append hprefix tailTrace_884773
  have hstable : (prefixWord ++ tailWord_884773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884773).length < 2 ^ (prefixWord ++ tailWord_884773).sum := by decide
  have hdescent : baseEnd_884773 < baseStart_884773 := by decide
  rcases family_descends (prefixWord ++ tailWord_884773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884787 : List Nat := [1, 1, 1, 2, 4, 1, 3, 5, 1, 2, 2]
def baseStart_884787 : Nat := 118140960795 + 884787 * 2 ^ 59
def prefixEnd_884787 : Nat := 4983230072969 + 3 ^ 40 * 884787 * 2
def baseEnd_884787 : Nat := 454321007849735000493445

theorem tailTrace_884787 : CollatzResearch.WordTrace tailWord_884787 prefixEnd_884787 454321007849735000493445 := by
  unfold tailWord_884787
  simp only [CollatzResearch.WordTrace]
  refine ⟨32270833045575283434260615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21513888697050188956173743 32270833045575283434260615)
  ·
    refine ⟨48406249568362925151390923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32270833045575283434260615 48406249568362925151390923)
    ·
      refine ⟨72609374352544387727086385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48406249568362925151390923 72609374352544387727086385)
      ·
        refine ⟨54457030764408290795314789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72609374352544387727086385 54457030764408290795314789)
        ·
          refine ⟨10210693268326554524121523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54457030764408290795314789 10210693268326554524121523)
          ·
            refine ⟨15316039902489831786182285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10210693268326554524121523 15316039902489831786182285)
            ·
              refine ⟨5743514963433686919818357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15316039902489831786182285 5743514963433686919818357)
              ·
                refine ⟨538454527821908148732971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5743514963433686919818357 538454527821908148732971)
                ·
                  refine ⟨807681791732862223099457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 538454527821908148732971 807681791732862223099457)
                  ·
                    refine ⟨605761343799646667324593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 807681791732862223099457 605761343799646667324593)
                    ·
                      refine ⟨454321007849735000493445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 605761343799646667324593 454321007849735000493445)
                      ·
                        rfl

theorem cell23_884787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 5, 1, 2, 2].length) (baseStart_884787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_884787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_884787 prefixEnd_884787 := by exact prefixLift 884787
  have htrace : WordTrace (prefixWord ++ tailWord_884787) baseStart_884787 baseEnd_884787 := by
    simpa [prefixWord, tailWord_884787, baseEnd_884787] using wordTrace_append hprefix tailTrace_884787
  have hstable : (prefixWord ++ tailWord_884787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884787).length < 2 ^ (prefixWord ++ tailWord_884787).sum := by decide
  have hdescent : baseEnd_884787 < baseStart_884787 := by decide
  rcases family_descends (prefixWord ++ tailWord_884787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884836 : List Nat := [2, 3, 1, 1, 2, 1, 2, 2, 1, 8]
def baseStart_884836 : Nat := 118140960795 + 884836 * 2 ^ 59
def prefixEnd_884836 : Nat := 4983230072969 + 3 ^ 40 * 884836 * 2
def baseEnd_884836 : Nat := 151448722800601769593573

theorem tailTrace_884836 : CollatzResearch.WordTrace tailWord_884836 prefixEnd_884836 151448722800601769593573 := by
  unfold tailWord_884836
  simp only [CollatzResearch.WordTrace]
  refine ⟨16136310111198882401397181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21515080148265176535196241 16136310111198882401397181)
  ·
    refine ⟨6051116291699580900523943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16136310111198882401397181 6051116291699580900523943)
    ·
      refine ⟨9076674437549371350785915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6051116291699580900523943 9076674437549371350785915)
      ·
        refine ⟨13615011656324057026178873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9076674437549371350785915 13615011656324057026178873)
        ·
          refine ⟨10211258742243042769634155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13615011656324057026178873 10211258742243042769634155)
          ·
            refine ⟨15316888113364564154451233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10211258742243042769634155 15316888113364564154451233)
            ·
              refine ⟨11487666085023423115838425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15316888113364564154451233 11487666085023423115838425)
              ·
                refine ⟨8615749563767567336878819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11487666085023423115838425 8615749563767567336878819)
                ·
                  refine ⟨12923624345651351005318229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8615749563767567336878819 12923624345651351005318229)
                  ·
                    refine ⟨151448722800601769593573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 12923624345651351005318229 151448722800601769593573)
                    ·
                      rfl

theorem cell23_884836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 1, 8].length) (baseStart_884836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_884836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_884836 prefixEnd_884836 := by exact prefixLift 884836
  have htrace : WordTrace (prefixWord ++ tailWord_884836) baseStart_884836 baseEnd_884836 := by
    simpa [prefixWord, tailWord_884836, baseEnd_884836] using wordTrace_append hprefix tailTrace_884836
  have hstable : (prefixWord ++ tailWord_884836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884836).length < 2 ^ (prefixWord ++ tailWord_884836).sum := by decide
  have hdescent : baseEnd_884836 < baseStart_884836 := by decide
  rcases family_descends (prefixWord ++ tailWord_884836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884894 : List Nat := [4, 3, 1, 1, 3, 1, 1, 2, 1, 4, 2]
def baseStart_884894 : Nat := 118140960795 + 884894 * 2 ^ 59
def prefixEnd_884894 : Nat := 4983230072969 + 3 ^ 40 * 884894 * 2
def baseEnd_884894 : Nat := 454375950279766081855453

theorem tailTrace_884894 : CollatzResearch.WordTrace tailWord_884894 prefixEnd_884894 454375950279766081855453 := by
  unfold tailWord_884894
  simp only [CollatzResearch.WordTrace]
  refine ⟨4034341957023455088550717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21516490437458427138937157 4034341957023455088550717)
  ·
    refine ⟨1512878233883795658206519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4034341957023455088550717 1512878233883795658206519)
    ·
      refine ⟨2269317350825693487309779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1512878233883795658206519 2269317350825693487309779)
      ·
        refine ⟨3403976026238540230964669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2269317350825693487309779 3403976026238540230964669)
        ·
          refine ⟨1276491009839452586611751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3403976026238540230964669 1276491009839452586611751)
          ·
            refine ⟨1914736514759178879917627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1276491009839452586611751 1914736514759178879917627)
            ·
              refine ⟨2872104772138768319876441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1914736514759178879917627 2872104772138768319876441)
              ·
                refine ⟨2154078579104076239907331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2872104772138768319876441 2154078579104076239907331)
                ·
                  refine ⟨3231117868656114359860997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2154078579104076239907331 3231117868656114359860997)
                  ·
                    refine ⟨605834600373021442473937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3231117868656114359860997 605834600373021442473937)
                    ·
                      refine ⟨454375950279766081855453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 605834600373021442473937 454375950279766081855453)
                      ·
                        rfl

theorem cell23_884894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_884894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_884894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_884894 prefixEnd_884894 := by exact prefixLift 884894
  have htrace : WordTrace (prefixWord ++ tailWord_884894) baseStart_884894 baseEnd_884894 := by
    simpa [prefixWord, tailWord_884894, baseEnd_884894] using wordTrace_append hprefix tailTrace_884894
  have hstable : (prefixWord ++ tailWord_884894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884894).length < 2 ^ (prefixWord ++ tailWord_884894).sum := by decide
  have hdescent : baseEnd_884894 < baseStart_884894 := by decide
  rcases family_descends (prefixWord ++ tailWord_884894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884933 : List Nat := [1, 3, 1, 1, 1, 1, 4, 2, 4, 1, 4]
def baseStart_884933 : Nat := 118140960795 + 884933 * 2 ^ 59
def prefixEnd_884933 : Nat := 4983230072969 + 3 ^ 40 * 884933 * 2
def baseEnd_884933 : Nat := 454395976025291429267773

theorem tailTrace_884933 : CollatzResearch.WordTrace tailWord_884933 prefixEnd_884933 454395976025291429267773 := by
  unfold tailWord_884933
  simp only [CollatzResearch.WordTrace]
  refine ⟨32276158103046350369075453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21517438735364233579383635 32276158103046350369075453)
  ·
    refine ⟨12103559288642381388403295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32276158103046350369075453 12103559288642381388403295)
    ·
      refine ⟨18155338932963572082604943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12103559288642381388403295 18155338932963572082604943)
      ·
        refine ⟨27233008399445358123907415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18155338932963572082604943 27233008399445358123907415)
        ·
          refine ⟨40849512599168037185861123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27233008399445358123907415 40849512599168037185861123)
          ·
            refine ⟨61274268898752055778791685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40849512599168037185861123 61274268898752055778791685)
            ·
              refine ⟨11488925418516010458523441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61274268898752055778791685 11488925418516010458523441)
              ·
                refine ⟨8616694063887007843892581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11488925418516010458523441 8616694063887007843892581)
                ·
                  refine ⟨1615630136978813970729859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8616694063887007843892581 1615630136978813970729859)
                  ·
                    refine ⟨2423445205468220956094789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1615630136978813970729859 2423445205468220956094789)
                    ·
                      refine ⟨454395976025291429267773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2423445205468220956094789 454395976025291429267773)
                      ·
                        rfl

theorem cell23_884933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 4, 1, 4].length) (baseStart_884933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_884933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_884933 prefixEnd_884933 := by exact prefixLift 884933
  have htrace : WordTrace (prefixWord ++ tailWord_884933) baseStart_884933 baseEnd_884933 := by
    simpa [prefixWord, tailWord_884933, baseEnd_884933] using wordTrace_append hprefix tailTrace_884933
  have hstable : (prefixWord ++ tailWord_884933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884933).length < 2 ^ (prefixWord ++ tailWord_884933).sum := by decide
  have hdescent : baseEnd_884933 < baseStart_884933 := by decide
  rcases family_descends (prefixWord ++ tailWord_884933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884962 : List Nat := [3, 3, 4, 1, 2, 1, 1, 2, 2, 2, 2]
def baseStart_884962 : Nat := 118140960795 + 884962 * 2 ^ 59
def prefixEnd_884962 : Nat := 4983230072969 + 3 ^ 40 * 884962 * 2
def baseEnd_884962 : Nat := 454410866964271815805141

theorem tailTrace_884962 : CollatzResearch.WordTrace tailWord_884962 prefixEnd_884962 454410866964271815805141 := by
  unfold tailWord_884962
  simp only [CollatzResearch.WordTrace]
  refine ⟨8069303954985322080470285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21518143879960858881254093 8069303954985322080470285)
  ·
    refine ⟨3025988983119495780176357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8069303954985322080470285 3025988983119495780176357)
    ·
      refine ⟨567372934334905458783067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3025988983119495780176357 567372934334905458783067)
      ·
        refine ⟨851059401502358188174601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 567372934334905458783067 851059401502358188174601)
        ·
          refine ⟨638294551126768641130951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 851059401502358188174601 638294551126768641130951)
          ·
            refine ⟨957441826690152961696427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 638294551126768641130951 957441826690152961696427)
            ·
              refine ⟨1436162740035229442544641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 957441826690152961696427 1436162740035229442544641)
              ·
                refine ⟨1077122055026422081908481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1436162740035229442544641 1077122055026422081908481)
                ·
                  refine ⟨807841541269816561431361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1077122055026422081908481 807841541269816561431361)
                  ·
                    refine ⟨605881155952362421073521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 807841541269816561431361 605881155952362421073521)
                    ·
                      refine ⟨454410866964271815805141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 605881155952362421073521 454410866964271815805141)
                      ·
                        rfl

theorem cell23_884962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_884962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_884962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_884962 prefixEnd_884962 := by exact prefixLift 884962
  have htrace : WordTrace (prefixWord ++ tailWord_884962) baseStart_884962 baseEnd_884962 := by
    simpa [prefixWord, tailWord_884962, baseEnd_884962] using wordTrace_append hprefix tailTrace_884962
  have hstable : (prefixWord ++ tailWord_884962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884962).length < 2 ^ (prefixWord ++ tailWord_884962).sum := by decide
  have hdescent : baseEnd_884962 < baseStart_884962 := by decide
  rcases family_descends (prefixWord ++ tailWord_884962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884967 : List Nat := [1, 1, 5, 3, 1, 1, 1, 2, 2, 4, 2]
def baseStart_884967 : Nat := 118140960795 + 884967 * 2 ^ 59
def prefixEnd_884967 : Nat := 4983230072969 + 3 ^ 40 * 884967 * 2
def baseEnd_884967 : Nat := 454413434367544296242617

theorem tailTrace_884967 : CollatzResearch.WordTrace tailWord_884967 prefixEnd_884967 454413434367544296242617 := by
  unfold tailWord_884967
  simp only [CollatzResearch.WordTrace]
  refine ⟨32277398184923174175813155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21518265456615449450542103 32277398184923174175813155)
  ·
    refine ⟨48416097277384761263719733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32277398184923174175813155 48416097277384761263719733)
    ·
      refine ⟨4539009119754821368473725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48416097277384761263719733 4539009119754821368473725)
      ·
        refine ⟨1702128419908058013177647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4539009119754821368473725 1702128419908058013177647)
        ·
          refine ⟨2553192629862087019766471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1702128419908058013177647 2553192629862087019766471)
          ·
            refine ⟨3829788944793130529649707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2553192629862087019766471 3829788944793130529649707)
            ·
              refine ⟨5744683417189695794474561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3829788944793130529649707 5744683417189695794474561)
              ·
                refine ⟨4308512562892271845855921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5744683417189695794474561 4308512562892271845855921)
                ·
                  refine ⟨3231384422169203884391941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4308512562892271845855921 3231384422169203884391941)
                  ·
                    refine ⟨605884579156725728323489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3231384422169203884391941 605884579156725728323489)
                    ·
                      refine ⟨454413434367544296242617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 605884579156725728323489 454413434367544296242617)
                      ·
                        rfl

theorem cell23_884967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_884967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_884967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_884967 prefixEnd_884967 := by exact prefixLift 884967
  have htrace : WordTrace (prefixWord ++ tailWord_884967) baseStart_884967 baseEnd_884967 := by
    simpa [prefixWord, tailWord_884967, baseEnd_884967] using wordTrace_append hprefix tailTrace_884967
  have hstable : (prefixWord ++ tailWord_884967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884967).length < 2 ^ (prefixWord ++ tailWord_884967).sum := by decide
  have hdescent : baseEnd_884967 < baseStart_884967 := by decide
  rcases family_descends (prefixWord ++ tailWord_884967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884970 : List Nat := [3, 1, 3, 1, 1, 2, 2, 1, 4, 2, 3]
def baseStart_884970 : Nat := 118140960795 + 884970 * 2 ^ 59
def prefixEnd_884970 : Nat := 4983230072969 + 3 ^ 40 * 884970 * 2
def baseEnd_884970 : Nat := 454414974809507784505103

theorem tailTrace_884970 : CollatzResearch.WordTrace tailWord_884970 prefixEnd_884970 454414974809507784505103 := by
  unfold tailWord_884970
  simp only [CollatzResearch.WordTrace]
  refine ⟨8069376900978076422043091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21518338402608203792114909 8069376900978076422043091)
  ·
    refine ⟨12104065351467114633064637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8069376900978076422043091 12104065351467114633064637)
    ·
      refine ⟨4539024506800167987399239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12104065351467114633064637 4539024506800167987399239)
      ·
        refine ⟨6808536760200251981098859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4539024506800167987399239 6808536760200251981098859)
        ·
          refine ⟨10212805140300377971648289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6808536760200251981098859 10212805140300377971648289)
          ·
            refine ⟨7659603855225283478736217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10212805140300377971648289 7659603855225283478736217)
            ·
              refine ⟨5744702891418962609052163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7659603855225283478736217 5744702891418962609052163)
              ·
                refine ⟨8617054337128443913578245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5744702891418962609052163 8617054337128443913578245)
                ·
                  refine ⟨1615697688211583233795921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8617054337128443913578245 1615697688211583233795921)
                  ·
                    refine ⟨1211773266158687425346941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1615697688211583233795921 1211773266158687425346941)
                    ·
                      refine ⟨454414974809507784505103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1211773266158687425346941 454414974809507784505103)
                      ·
                        rfl

theorem cell23_884970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_884970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_884970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_884970 prefixEnd_884970 := by exact prefixLift 884970
  have htrace : WordTrace (prefixWord ++ tailWord_884970) baseStart_884970 baseEnd_884970 := by
    simpa [prefixWord, tailWord_884970, baseEnd_884970] using wordTrace_append hprefix tailTrace_884970
  have hstable : (prefixWord ++ tailWord_884970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884970).length < 2 ^ (prefixWord ++ tailWord_884970).sum := by decide
  have hdescent : baseEnd_884970 < baseStart_884970 := by decide
  rcases family_descends (prefixWord ++ tailWord_884970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884977 : List Nat := [1, 2, 2, 2, 2, 1, 4, 4, 1, 4]
def baseStart_884977 : Nat := 118140960795 + 884977 * 2 ^ 59
def prefixEnd_884977 : Nat := 4983230072969 + 3 ^ 40 * 884977 * 2
def baseEnd_884977 : Nat := 151472856391363085705857

theorem tailTrace_884977 : CollatzResearch.WordTrace tailWord_884977 prefixEnd_884977 151472856391363085705857 := by
  unfold tailWord_884977
  simp only [CollatzResearch.WordTrace]
  refine ⟨32277762914886945883677185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21518508609924630589118123 32277762914886945883677185)
  ·
    refine ⟨24208322186165209412757889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32277762914886945883677185 24208322186165209412757889)
    ·
      refine ⟨18156241639623907059568417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24208322186165209412757889 18156241639623907059568417)
      ·
        refine ⟨13617181229717930294676313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18156241639623907059568417 13617181229717930294676313)
        ·
          refine ⟨10212885922288447721007235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13617181229717930294676313 10212885922288447721007235)
          ·
            refine ⟨15319328883432671581510853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10212885922288447721007235 15319328883432671581510853)
            ·
              refine ⟨2872374165643625921533285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15319328883432671581510853 2872374165643625921533285)
              ·
                refine ⟨538570156058179860287491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2872374165643625921533285 538570156058179860287491)
                ·
                  refine ⟨807855234087269790431237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 538570156058179860287491 807855234087269790431237)
                  ·
                    refine ⟨151472856391363085705857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 807855234087269790431237 151472856391363085705857)
                    ·
                      rfl

theorem cell23_884977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 4, 1, 4].length) (baseStart_884977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_884977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_884977 prefixEnd_884977 := by exact prefixLift 884977
  have htrace : WordTrace (prefixWord ++ tailWord_884977) baseStart_884977 baseEnd_884977 := by
    simpa [prefixWord, tailWord_884977, baseEnd_884977] using wordTrace_append hprefix tailTrace_884977
  have hstable : (prefixWord ++ tailWord_884977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884977).length < 2 ^ (prefixWord ++ tailWord_884977).sum := by decide
  have hdescent : baseEnd_884977 < baseStart_884977 := by decide
  rcases family_descends (prefixWord ++ tailWord_884977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884983 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 4, 5, 3]
def baseStart_884983 : Nat := 118140960795 + 884983 * 2 ^ 59
def prefixEnd_884983 : Nat := 4983230072969 + 3 ^ 40 * 884983 * 2
def baseEnd_884983 : Nat := 454421650058016233642543

theorem tailTrace_884983 : CollatzResearch.WordTrace tailWord_884983 prefixEnd_884983 454421650058016233642543 := by
  unfold tailWord_884983
  simp only [CollatzResearch.WordTrace]
  refine ⟨32277981752865208908395603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21518654501910139272263735 32277981752865208908395603)
  ·
    refine ⟨48416972629297813362593405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32277981752865208908395603 48416972629297813362593405)
    ·
      refine ⟨18156364735986680010972527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48416972629297813362593405 18156364735986680010972527)
      ·
        refine ⟨27234547103980020016458791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18156364735986680010972527 27234547103980020016458791)
        ·
          refine ⟨40851820655970030024688187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27234547103980020016458791 40851820655970030024688187)
          ·
            refine ⟨61277730983955045037032281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40851820655970030024688187 61277730983955045037032281)
            ·
              refine ⟨45958298237966283777774211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61277730983955045037032281 45958298237966283777774211)
              ·
                refine ⟨68937447356949425666661317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45958298237966283777774211 68937447356949425666661317)
                ·
                  refine ⟨12925771379428017312498997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68937447356949425666661317 12925771379428017312498997)
                  ·
                    refine ⟨1211791066821376623046781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12925771379428017312498997 1211791066821376623046781)
                    ·
                      refine ⟨454421650058016233642543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1211791066821376623046781 454421650058016233642543)
                      ·
                        rfl

theorem cell23_884983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 5, 3].length) (baseStart_884983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_884983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_884983 prefixEnd_884983 := by exact prefixLift 884983
  have htrace : WordTrace (prefixWord ++ tailWord_884983) baseStart_884983 baseEnd_884983 := by
    simpa [prefixWord, tailWord_884983, baseEnd_884983] using wordTrace_append hprefix tailTrace_884983
  have hstable : (prefixWord ++ tailWord_884983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884983).length < 2 ^ (prefixWord ++ tailWord_884983).sum := by decide
  have hdescent : baseEnd_884983 < baseStart_884983 := by decide
  rcases family_descends (prefixWord ++ tailWord_884983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884993 : List Nat := [1, 2, 4, 1, 1, 2, 1, 2, 1, 2, 6]
def baseStart_884993 : Nat := 118140960795 + 884993 * 2 ^ 59
def prefixEnd_884993 : Nat := 4983230072969 + 3 ^ 40 * 884993 * 2
def baseEnd_884993 : Nat := 454426784864561194517497

theorem tailTrace_884993 : CollatzResearch.WordTrace tailWord_884993 prefixEnd_884993 454426784864561194517497 := by
  unfold tailWord_884993
  simp only [CollatzResearch.WordTrace]
  refine ⟨32278346482828980616259633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21518897655219320410839755 32278346482828980616259633)
  ·
    refine ⟨24208759862121735462194725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32278346482828980616259633 24208759862121735462194725)
    ·
      refine ⟨4539142474147825399161511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24208759862121735462194725 4539142474147825399161511)
      ·
        refine ⟨6808713711221738098742267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4539142474147825399161511 6808713711221738098742267)
        ·
          refine ⟨10213070566832607148113401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6808713711221738098742267 10213070566832607148113401)
          ·
            refine ⟨7659802925124455361085051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10213070566832607148113401 7659802925124455361085051)
            ·
              refine ⟨11489704387686683041627577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7659802925124455361085051 11489704387686683041627577)
              ·
                refine ⟨8617278290765012281220683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11489704387686683041627577 8617278290765012281220683)
                ·
                  refine ⟨12925917436147518421831025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8617278290765012281220683 12925917436147518421831025)
                  ·
                    refine ⟨9694438077110638816373269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12925917436147518421831025 9694438077110638816373269)
                    ·
                      refine ⟨454426784864561194517497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9694438077110638816373269 454426784864561194517497)
                      ·
                        rfl

theorem cell23_884993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_884993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_884993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_884993 prefixEnd_884993 := by exact prefixLift 884993
  have htrace : WordTrace (prefixWord ++ tailWord_884993) baseStart_884993 baseEnd_884993 := by
    simpa [prefixWord, tailWord_884993, baseEnd_884993] using wordTrace_append hprefix tailTrace_884993
  have hstable : (prefixWord ++ tailWord_884993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884993).length < 2 ^ (prefixWord ++ tailWord_884993).sum := by decide
  have hdescent : baseEnd_884993 < baseStart_884993 := by decide
  rcases family_descends (prefixWord ++ tailWord_884993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885027 : List Nat := [1, 1, 1, 4, 2, 2, 3, 2, 2, 3, 2]
def baseStart_885027 : Nat := 118140960795 + 885027 * 2 ^ 59
def prefixEnd_885027 : Nat := 4983230072969 + 3 ^ 40 * 885027 * 2
def baseEnd_885027 : Nat := 454444243206814061492341

theorem tailTrace_885027 : CollatzResearch.WordTrace tailWord_885027 prefixEnd_885027 454444243206814061492341 := by
  unfold tailWord_885027
  simp only [CollatzResearch.WordTrace]
  refine ⟨32279586564705804422997335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21519724376470536281998223 32279586564705804422997335)
  ·
    refine ⟨48419379847058706634496003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32279586564705804422997335 48419379847058706634496003)
    ·
      refine ⟨72629069770588059951744005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48419379847058706634496003 72629069770588059951744005)
      ·
        refine ⟨13617950581985261240952001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72629069770588059951744005 13617950581985261240952001)
        ·
          refine ⟨10213462936488945930714001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13617950581985261240952001 10213462936488945930714001)
          ·
            refine ⟨7660097202366709448035501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10213462936488945930714001 7660097202366709448035501)
            ·
              refine ⟨2872536450887516043013313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7660097202366709448035501 2872536450887516043013313)
              ·
                refine ⟨2154402338165637032259985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2872536450887516043013313 2154402338165637032259985)
                ·
                  refine ⟨1615801753624227774194989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2154402338165637032259985 1615801753624227774194989)
                  ·
                    refine ⟨605925657609085415323121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1615801753624227774194989 605925657609085415323121)
                    ·
                      refine ⟨454444243206814061492341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 605925657609085415323121 454444243206814061492341)
                      ·
                        rfl

theorem cell23_885027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 2, 2, 3, 2].length) (baseStart_885027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_885027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_885027 prefixEnd_885027 := by exact prefixLift 885027
  have htrace : WordTrace (prefixWord ++ tailWord_885027) baseStart_885027 baseEnd_885027 := by
    simpa [prefixWord, tailWord_885027, baseEnd_885027] using wordTrace_append hprefix tailTrace_885027
  have hstable : (prefixWord ++ tailWord_885027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885027).length < 2 ^ (prefixWord ++ tailWord_885027).sum := by decide
  have hdescent : baseEnd_885027 < baseStart_885027 := by decide
  rcases family_descends (prefixWord ++ tailWord_885027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885040 : List Nat := [2, 1, 1, 1, 2, 2, 2, 2, 2, 6, 2]
def baseStart_885040 : Nat := 118140960795 + 885040 * 2 ^ 59
def prefixEnd_885040 : Nat := 4983230072969 + 3 ^ 40 * 885040 * 2
def baseEnd_885040 : Nat := 454450918455322510629781

theorem tailTrace_885040 : CollatzResearch.WordTrace tailWord_885040 prefixEnd_885040 454450918455322510629781 := by
  unfold tailWord_885040
  simp only [CollatzResearch.WordTrace]
  refine ⟨16140030356829353821610287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21520040475772471762147049 16140030356829353821610287)
  ·
    refine ⟨24210045535244030732415431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16140030356829353821610287 24210045535244030732415431)
    ·
      refine ⟨36315068302866046098623147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24210045535244030732415431 36315068302866046098623147)
      ·
        refine ⟨54472602454299069147934721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36315068302866046098623147 54472602454299069147934721)
        ·
          refine ⟨40854451840724301860951041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54472602454299069147934721 40854451840724301860951041)
          ·
            refine ⟨30640838880543226395713281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40854451840724301860951041 30640838880543226395713281)
            ·
              refine ⟨22980629160407419796784961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30640838880543226395713281 22980629160407419796784961)
              ·
                refine ⟨17235471870305564847588721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22980629160407419796784961 17235471870305564847588721)
                ·
                  refine ⟨12926603902729173635691541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17235471870305564847588721 12926603902729173635691541)
                  ·
                    refine ⟨605934557940430014173041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12926603902729173635691541 605934557940430014173041)
                    ·
                      refine ⟨454450918455322510629781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 605934557940430014173041 454450918455322510629781)
                      ·
                        rfl

theorem cell23_885040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 2, 6, 2].length) (baseStart_885040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_885040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_885040 prefixEnd_885040 := by exact prefixLift 885040
  have htrace : WordTrace (prefixWord ++ tailWord_885040) baseStart_885040 baseEnd_885040 := by
    simpa [prefixWord, tailWord_885040, baseEnd_885040] using wordTrace_append hprefix tailTrace_885040
  have hstable : (prefixWord ++ tailWord_885040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885040).length < 2 ^ (prefixWord ++ tailWord_885040).sum := by decide
  have hdescent : baseEnd_885040 < baseStart_885040 := by decide
  rcases family_descends (prefixWord ++ tailWord_885040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885054 : List Nat := [4, 2, 1, 2, 1, 4, 1, 2, 1, 5]
def baseStart_885054 : Nat := 118140960795 + 885054 * 2 ^ 59
def prefixEnd_885054 : Nat := 4983230072969 + 3 ^ 40 * 885054 * 2
def baseEnd_885054 : Nat := 151486035728161818618239

theorem tailTrace_885054 : CollatzResearch.WordTrace tailWord_885054 prefixEnd_885054 151486035728161818618239 := by
  unfold tailWord_885054
  simp only [CollatzResearch.WordTrace]
  refine ⟨4035071416950998504278777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21520380890405325356153477 4035071416950998504278777)
  ·
    refine ⟨3026303562713248878209083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4035071416950998504278777 3026303562713248878209083)
    ·
      refine ⟨4539455344069873317313625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3026303562713248878209083 4539455344069873317313625)
      ·
        refine ⟨3404591508052404987985219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4539455344069873317313625 3404591508052404987985219)
        ·
          refine ⟨5106887262078607481977829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3404591508052404987985219 5106887262078607481977829)
          ·
            refine ⟨957541361639738902870843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5106887262078607481977829 957541361639738902870843)
            ·
              refine ⟨1436312042459608354306265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 957541361639738902870843 1436312042459608354306265)
              ·
                refine ⟨1077234031844706265729699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1436312042459608354306265 1077234031844706265729699)
                ·
                  refine ⟨1615851047767059398594549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1077234031844706265729699 1615851047767059398594549)
                  ·
                    refine ⟨151486035728161818618239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1615851047767059398594549 151486035728161818618239)
                    ·
                      rfl

theorem cell23_885054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_885054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_885054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_885054 prefixEnd_885054 := by exact prefixLift 885054
  have htrace : WordTrace (prefixWord ++ tailWord_885054) baseStart_885054 baseEnd_885054 := by
    simpa [prefixWord, tailWord_885054, baseEnd_885054] using wordTrace_append hprefix tailTrace_885054
  have hstable : (prefixWord ++ tailWord_885054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885054).length < 2 ^ (prefixWord ++ tailWord_885054).sum := by decide
  have hdescent : baseEnd_885054 < baseStart_885054 := by decide
  rcases family_descends (prefixWord ++ tailWord_885054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885063 : List Nat := [1, 1, 4, 1, 2, 2, 1, 11]
def baseStart_885063 : Nat := 118140960795 + 885063 * 2 ^ 59
def prefixEnd_885063 : Nat := 4983230072969 + 3 ^ 40 * 885063 * 2
def baseEnd_885063 : Nat := 16831952907791700764525

theorem tailTrace_885063 : CollatzResearch.WordTrace tailWord_885063 prefixEnd_885063 16831952907791700764525 := by
  unfold tailWord_885063
  simp only [CollatzResearch.WordTrace]
  refine ⟨32280899592575382571307843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21520599728383588380871895 32280899592575382571307843)
  ·
    refine ⟨48421349388863073856961765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32280899592575382571307843 48421349388863073856961765)
    ·
      refine ⟨9079003010411826348180331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48421349388863073856961765 9079003010411826348180331)
      ·
        refine ⟨13618504515617739522270497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9079003010411826348180331 13618504515617739522270497)
        ·
          refine ⟨10213878386713304641702873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13618504515617739522270497 10213878386713304641702873)
          ·
            refine ⟨7660408790034978481277155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10213878386713304641702873 7660408790034978481277155)
            ·
              refine ⟨11490613185052467721915733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7660408790034978481277155 11490613185052467721915733)
              ·
                refine ⟨16831952907791700764525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 11490613185052467721915733 16831952907791700764525)
                ·
                  rfl

theorem cell23_885063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 11].length) (baseStart_885063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_885063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_885063 prefixEnd_885063 := by exact prefixLift 885063
  have htrace : WordTrace (prefixWord ++ tailWord_885063) baseStart_885063 baseEnd_885063 := by
    simpa [prefixWord, tailWord_885063, baseEnd_885063] using wordTrace_append hprefix tailTrace_885063
  have hstable : (prefixWord ++ tailWord_885063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885063).length < 2 ^ (prefixWord ++ tailWord_885063).sum := by decide
  have hdescent : baseEnd_885063 < baseStart_885063 := by decide
  rcases family_descends (prefixWord ++ tailWord_885063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885091 : List Nat := [1, 1, 1, 5, 2, 1, 3, 4, 1, 2, 2]
def baseStart_885091 : Nat := 118140960795 + 885091 * 2 ^ 59
def prefixEnd_885091 : Nat := 4983230072969 + 3 ^ 40 * 885091 * 2
def baseEnd_885091 : Nat := 454477105968701811092047

theorem tailTrace_885091 : CollatzResearch.WordTrace tailWord_885091 prefixEnd_885091 454477105968701811092047 := by
  unfold tailWord_885091
  simp only [CollatzResearch.WordTrace]
  refine ⟨32281920836473943353327127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21521280557649295568884751 32281920836473943353327127)
  ·
    refine ⟨48422881254710915029990691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32281920836473943353327127 48422881254710915029990691)
    ·
      refine ⟨72634321882066372544986037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48422881254710915029990691 72634321882066372544986037)
      ·
        refine ⟨6809467676443722426092441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72634321882066372544986037 6809467676443722426092441)
        ·
          refine ⟨5107100757332791819569331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6809467676443722426092441 5107100757332791819569331)
          ·
            refine ⟨7660651135999187729353997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5107100757332791819569331 7660651135999187729353997)
            ·
              refine ⟨2872744175999695398507749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7660651135999187729353997 2872744175999695398507749)
              ·
                refine ⟨538639532999942887220203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2872744175999695398507749 538639532999942887220203)
                ·
                  refine ⟨807959299499914330830305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 538639532999942887220203 807959299499914330830305)
                  ·
                    refine ⟨605969474624935748122729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 807959299499914330830305 605969474624935748122729)
                    ·
                      refine ⟨454477105968701811092047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 605969474624935748122729 454477105968701811092047)
                      ·
                        rfl

theorem cell23_885091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 4, 1, 2, 2].length) (baseStart_885091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_885091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_885091 prefixEnd_885091 := by exact prefixLift 885091
  have htrace : WordTrace (prefixWord ++ tailWord_885091) baseStart_885091 baseEnd_885091 := by
    simpa [prefixWord, tailWord_885091, baseEnd_885091] using wordTrace_append hprefix tailTrace_885091
  have hstable : (prefixWord ++ tailWord_885091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885091).length < 2 ^ (prefixWord ++ tailWord_885091).sum := by decide
  have hdescent : baseEnd_885091 < baseStart_885091 := by decide
  rcases family_descends (prefixWord ++ tailWord_885091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885142 : List Nat := [5, 3, 1, 2, 1, 1, 2, 1, 3, 2, 2]
def baseStart_885142 : Nat := 118140960795 + 885142 * 2 ^ 59
def prefixEnd_885142 : Nat := 4983230072969 + 3 ^ 40 * 885142 * 2
def baseEnd_885142 : Nat := 454503293482081111554313

theorem tailTrace_885142 : CollatzResearch.WordTrace tailWord_885142 prefixEnd_885142 454503293482081111554313 := by
  unfold tailWord_885142
  simp only [CollatzResearch.WordTrace]
  refine ⟨2017736309955573691464605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21522520639526119375622453 2017736309955573691464605)
  ·
    refine ⟨756651116233340134299227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2017736309955573691464605 756651116233340134299227)
    ·
      refine ⟨1134976674350010201448841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 756651116233340134299227 1134976674350010201448841)
      ·
        refine ⟨851232505762507651086631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1134976674350010201448841 851232505762507651086631)
        ·
          refine ⟨1276848758643761476629947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 851232505762507651086631 1276848758643761476629947)
          ·
            refine ⟨1915273137965642214944921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1276848758643761476629947 1915273137965642214944921)
            ·
              refine ⟨1436454853474231661208691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1915273137965642214944921 1436454853474231661208691)
              ·
                refine ⟨2154682280211347491813037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1436454853474231661208691 2154682280211347491813037)
                ·
                  refine ⟨808005855079255309429889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2154682280211347491813037 808005855079255309429889)
                  ·
                    refine ⟨606004391309441482072417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 808005855079255309429889 606004391309441482072417)
                    ·
                      refine ⟨454503293482081111554313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 606004391309441482072417 454503293482081111554313)
                      ·
                        rfl

theorem cell23_885142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_885142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_885142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_885142 prefixEnd_885142 := by exact prefixLift 885142
  have htrace : WordTrace (prefixWord ++ tailWord_885142) baseStart_885142 baseEnd_885142 := by
    simpa [prefixWord, tailWord_885142, baseEnd_885142] using wordTrace_append hprefix tailTrace_885142
  have hstable : (prefixWord ++ tailWord_885142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885142).length < 2 ^ (prefixWord ++ tailWord_885142).sum := by decide
  have hdescent : baseEnd_885142 < baseStart_885142 := by decide
  rcases family_descends (prefixWord ++ tailWord_885142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885170 : List Nat := [3, 2, 1, 1, 1, 1, 3, 4, 7]
def baseStart_885170 : Nat := 118140960795 + 885170 * 2 ^ 59
def prefixEnd_885170 : Nat := 4983230072969 + 3 ^ 40 * 885170 * 2
def baseEnd_885170 : Nat := 50501963437823000222687

theorem tailTrace_885170 : CollatzResearch.WordTrace tailWord_885170 prefixEnd_885170 50501963437823000222687 := by
  unfold tailWord_885170
  simp only [CollatzResearch.WordTrace]
  refine ⟨8071200550796934961363241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21523201468791826563635309 8071200550796934961363241)
  ·
    refine ⟨6053400413097701221022431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8071200550796934961363241 6053400413097701221022431)
    ·
      refine ⟨9080100619646551831533647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6053400413097701221022431 9080100619646551831533647)
      ·
        refine ⟨13620150929469827747300471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9080100619646551831533647 13620150929469827747300471)
        ·
          refine ⟨20430226394204741620950707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13620150929469827747300471 20430226394204741620950707)
          ·
            refine ⟨30645339591307112431426061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20430226394204741620950707 30645339591307112431426061)
            ·
              refine ⟨11492002346740167161784773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30645339591307112431426061 11492002346740167161784773)
              ·
                refine ⟨2154750440013781342834645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11492002346740167161784773 2154750440013781342834645)
                ·
                  refine ⟨50501963437823000222687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2154750440013781342834645 50501963437823000222687)
                  ·
                    rfl

theorem cell23_885170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4, 7].length) (baseStart_885170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_885170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_885170 prefixEnd_885170 := by exact prefixLift 885170
  have htrace : WordTrace (prefixWord ++ tailWord_885170) baseStart_885170 baseEnd_885170 := by
    simpa [prefixWord, tailWord_885170, baseEnd_885170] using wordTrace_append hprefix tailTrace_885170
  have hstable : (prefixWord ++ tailWord_885170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885170).length < 2 ^ (prefixWord ++ tailWord_885170).sum := by decide
  have hdescent : baseEnd_885170 < baseStart_885170 := by decide
  rcases family_descends (prefixWord ++ tailWord_885170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885204 : List Nat := [2, 4, 1, 2, 2, 3, 1, 1, 7]
def baseStart_885204 : Nat := 118140960795 + 885204 * 2 ^ 59
def prefixEnd_885204 : Nat := 4983230072969 + 3 ^ 40 * 885204 * 2
def baseEnd_885204 : Nat := 50503903253628874331003

theorem tailTrace_885204 : CollatzResearch.WordTrace tailWord_885204 prefixEnd_885204 50503903253628874331003 := by
  unfold tailWord_885204
  simp only [CollatzResearch.WordTrace]
  refine ⟨16143021142532281826095333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21524028190043042434793777 16143021142532281826095333)
  ·
    refine ⟨3026816464224802842392875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16143021142532281826095333 3026816464224802842392875)
    ·
      refine ⟨4540224696337204263589313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3026816464224802842392875 4540224696337204263589313)
      ·
        refine ⟨3405168522252903197691985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4540224696337204263589313 3405168522252903197691985)
        ·
          refine ⟨2553876391689677398268989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3405168522252903197691985 2553876391689677398268989)
          ·
            refine ⟨957703646883629024350871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2553876391689677398268989 957703646883629024350871)
            ·
              refine ⟨1436555470325443536526307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 957703646883629024350871 1436555470325443536526307)
              ·
                refine ⟨2154833205488165304789461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1436555470325443536526307 2154833205488165304789461)
                ·
                  refine ⟨50503903253628874331003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2154833205488165304789461 50503903253628874331003)
                  ·
                    rfl

theorem cell23_885204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 1, 7].length) (baseStart_885204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_885204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_885204 prefixEnd_885204 := by exact prefixLift 885204
  have htrace : WordTrace (prefixWord ++ tailWord_885204) baseStart_885204 baseEnd_885204 := by
    simpa [prefixWord, tailWord_885204, baseEnd_885204] using wordTrace_append hprefix tailTrace_885204
  have hstable : (prefixWord ++ tailWord_885204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885204).length < 2 ^ (prefixWord ++ tailWord_885204).sum := by decide
  have hdescent : baseEnd_885204 < baseStart_885204 := by decide
  rcases family_descends (prefixWord ++ tailWord_885204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885257 : List Nat := [1, 2, 1, 1, 3, 1, 2, 3, 4, 2, 3]
def baseStart_885257 : Nat := 118140960795 + 885257 * 2 ^ 59
def prefixEnd_885257 : Nat := 4983230072969 + 3 ^ 40 * 885257 * 2
def baseEnd_885257 : Nat := 454562343757348161616283

theorem tailTrace_885257 : CollatzResearch.WordTrace tailWord_885257 prefixEnd_885257 454562343757348161616283 := by
  unfold tailWord_885257
  simp only [CollatzResearch.WordTrace]
  refine ⟨32287975353872553703870025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21525316902581702469246683 32287975353872553703870025)
  ·
    refine ⟨24215981515404415277902519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32287975353872553703870025 24215981515404415277902519)
    ·
      refine ⟨36323972273106622916853779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24215981515404415277902519 36323972273106622916853779)
      ·
        refine ⟨54485958409659934375280669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36323972273106622916853779 54485958409659934375280669)
        ·
          refine ⟨20432234403622475390730251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54485958409659934375280669 20432234403622475390730251)
          ·
            refine ⟨30648351605433713086095377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20432234403622475390730251 30648351605433713086095377)
            ·
              refine ⟨22986263704075284814571533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30648351605433713086095377 22986263704075284814571533)
              ·
                refine ⟨8619848889028231805464325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22986263704075284814571533 8619848889028231805464325)
                ·
                  refine ⟨1616221666692793463524561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8619848889028231805464325 1616221666692793463524561)
                  ·
                    refine ⟨1212166250019595097643421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1616221666692793463524561 1212166250019595097643421)
                    ·
                      refine ⟨454562343757348161616283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1212166250019595097643421 454562343757348161616283)
                      ·
                        rfl

theorem cell23_885257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 4, 2, 3].length) (baseStart_885257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_885257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_885257 prefixEnd_885257 := by exact prefixLift 885257
  have htrace : WordTrace (prefixWord ++ tailWord_885257) baseStart_885257 baseEnd_885257 := by
    simpa [prefixWord, tailWord_885257, baseEnd_885257] using wordTrace_append hprefix tailTrace_885257
  have hstable : (prefixWord ++ tailWord_885257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885257).length < 2 ^ (prefixWord ++ tailWord_885257).sum := by decide
  have hdescent : baseEnd_885257 < baseStart_885257 := by decide
  rcases family_descends (prefixWord ++ tailWord_885257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885261 : List Nat := [1, 7, 1, 1, 1, 1, 2, 1, 1, 2, 5]
def baseStart_885261 : Nat := 118140960795 + 885261 * 2 ^ 59
def prefixEnd_885261 : Nat := 4983230072969 + 3 ^ 40 * 885261 * 2
def baseEnd_885261 : Nat := 454564397679966145966265

theorem tailTrace_885261 : CollatzResearch.WordTrace tailWord_885261 prefixEnd_885261 454564397679966145966265 := by
  unfold tailWord_885261
  simp only [CollatzResearch.WordTrace]
  refine ⟨32288121245858062387015637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21525414163905374924677091 32288121245858062387015637)
  ·
    refine ⟨756752841699798337195679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 32288121245858062387015637 756752841699798337195679)
    ·
      refine ⟨1135129262549697505793519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 756752841699798337195679 1135129262549697505793519)
      ·
        refine ⟨1702693893824546258690279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1135129262549697505793519 1702693893824546258690279)
        ·
          refine ⟨2554040840736819388035419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1702693893824546258690279 2554040840736819388035419)
          ·
            refine ⟨3831061261105229082053129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2554040840736819388035419 3831061261105229082053129)
            ·
              refine ⟨2873295945828921811539847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3831061261105229082053129 2873295945828921811539847)
              ·
                refine ⟨4309943918743382717309771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2873295945828921811539847 4309943918743382717309771)
                ·
                  refine ⟨6464915878115074075964657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4309943918743382717309771 6464915878115074075964657)
                  ·
                    refine ⟨4848686908586305556973493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6464915878115074075964657 4848686908586305556973493)
                    ·
                      refine ⟨454564397679966145966265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4848686908586305556973493 454564397679966145966265)
                      ·
                        rfl

theorem cell23_885261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_885261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_885261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_885261 prefixEnd_885261 := by exact prefixLift 885261
  have htrace : WordTrace (prefixWord ++ tailWord_885261) baseStart_885261 baseEnd_885261 := by
    simpa [prefixWord, tailWord_885261, baseEnd_885261] using wordTrace_append hprefix tailTrace_885261
  have hstable : (prefixWord ++ tailWord_885261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885261).length < 2 ^ (prefixWord ++ tailWord_885261).sum := by decide
  have hdescent : baseEnd_885261 < baseStart_885261 := by decide
  rcases family_descends (prefixWord ++ tailWord_885261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885304 : List Nat := [2, 1, 2, 1, 4, 1, 1, 2, 5, 1, 3]
def baseStart_885304 : Nat := 118140960795 + 885304 * 2 ^ 59
def prefixEnd_885304 : Nat := 4983230072969 + 3 ^ 40 * 885304 * 2
def baseEnd_885304 : Nat := 454586477348109477728567

theorem tailTrace_885304 : CollatzResearch.WordTrace tailWord_885304 prefixEnd_885304 454586477348109477728567 := by
  unfold tailWord_885304
  simp only [CollatzResearch.WordTrace]
  refine ⟨16144844792351140365415483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21526459723134853820553977 16144844792351140365415483)
  ·
    refine ⟨24217267188526710548123225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16144844792351140365415483 24217267188526710548123225)
    ·
      refine ⟨18162950391395032911092419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24217267188526710548123225 18162950391395032911092419)
      ·
        refine ⟨27244425587092549366638629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18162950391395032911092419 27244425587092549366638629)
        ·
          refine ⟨5108329797579853006244743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27244425587092549366638629 5108329797579853006244743)
          ·
            refine ⟨7662494696369779509367115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5108329797579853006244743 7662494696369779509367115)
            ·
              refine ⟨11493742044554669264050673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7662494696369779509367115 11493742044554669264050673)
              ·
                refine ⟨8620306533416001948038005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11493742044554669264050673 8620306533416001948038005)
                ·
                  refine ⟨808153737507750182628563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8620306533416001948038005 808153737507750182628563)
                  ·
                    refine ⟨1212230606261625273942845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 808153737507750182628563 1212230606261625273942845)
                    ·
                      refine ⟨454586477348109477728567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1212230606261625273942845 454586477348109477728567)
                      ·
                        rfl

theorem cell23_885304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 5, 1, 3].length) (baseStart_885304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_885304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_885304 prefixEnd_885304 := by exact prefixLift 885304
  have htrace : WordTrace (prefixWord ++ tailWord_885304) baseStart_885304 baseEnd_885304 := by
    simpa [prefixWord, tailWord_885304, baseEnd_885304] using wordTrace_append hprefix tailTrace_885304
  have hstable : (prefixWord ++ tailWord_885304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885304).length < 2 ^ (prefixWord ++ tailWord_885304).sum := by decide
  have hdescent : baseEnd_885304 < baseStart_885304 := by decide
  rcases family_descends (prefixWord ++ tailWord_885304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885327 : List Nat := [1, 1, 2, 1, 1, 2, 4, 1, 5, 1, 4]
def baseStart_885327 : Nat := 118140960795 + 885327 * 2 ^ 59
def prefixEnd_885327 : Nat := 4983230072969 + 3 ^ 40 * 885327 * 2
def baseEnd_885327 : Nat := 454598287403162887740961

theorem tailTrace_885327 : CollatzResearch.WordTrace tailWord_885327 prefixEnd_885327 454598287403162887740961 := by
  unfold tailWord_885327
  simp only [CollatzResearch.WordTrace]
  refine ⟨32290528463618955658918235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21527018975745970439278823 32290528463618955658918235)
  ·
    refine ⟨48435792695428433488377353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32290528463618955658918235 48435792695428433488377353)
    ·
      refine ⟨36326844521571325116283015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48435792695428433488377353 36326844521571325116283015)
      ·
        refine ⟨54490266782356987674424523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36326844521571325116283015 54490266782356987674424523)
        ·
          refine ⟨81735400173535481511636785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54490266782356987674424523 81735400173535481511636785)
          ·
            refine ⟨61301550130151611133727589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81735400173535481511636785 61301550130151611133727589)
            ·
              refine ⟨11494040649403427087573923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61301550130151611133727589 11494040649403427087573923)
              ·
                refine ⟨17241060974105140631360885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11494040649403427087573923 17241060974105140631360885)
                ·
                  refine ⟨1616349466322356934190083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17241060974105140631360885 1616349466322356934190083)
                  ·
                    refine ⟨2424524199483535401285125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1616349466322356934190083 2424524199483535401285125)
                    ·
                      refine ⟨454598287403162887740961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2424524199483535401285125 454598287403162887740961)
                      ·
                        rfl

theorem cell23_885327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 5, 1, 4].length) (baseStart_885327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_885327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_885327 prefixEnd_885327 := by exact prefixLift 885327
  have htrace : WordTrace (prefixWord ++ tailWord_885327) baseStart_885327 baseEnd_885327 := by
    simpa [prefixWord, tailWord_885327, baseEnd_885327] using wordTrace_append hprefix tailTrace_885327
  have hstable : (prefixWord ++ tailWord_885327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885327).length < 2 ^ (prefixWord ++ tailWord_885327).sum := by decide
  have hdescent : baseEnd_885327 < baseStart_885327 := by decide
  rcases family_descends (prefixWord ++ tailWord_885327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885344 : List Nat := [2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 4]
def baseStart_885344 : Nat := 118140960795 + 885344 * 2 ^ 59
def prefixEnd_885344 : Nat := 4983230072969 + 3 ^ 40 * 885344 * 2
def baseEnd_885344 : Nat := 454607016574289321228383

theorem tailTrace_885344 : CollatzResearch.WordTrace tailWord_885344 prefixEnd_885344 454607016574289321228383 := by
  unfold tailWord_885344
  simp only [CollatzResearch.WordTrace]
  refine ⟨16145574252278683781143543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21527432336371578374858057 16145574252278683781143543)
  ·
    refine ⟨24218361378418025671715315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16145574252278683781143543 24218361378418025671715315)
    ·
      refine ⟨36327542067627038507572973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24218361378418025671715315 36327542067627038507572973)
      ·
        refine ⟨13622828275360139440339865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36327542067627038507572973 13622828275360139440339865)
        ·
          refine ⟨10217121206520104580254899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13622828275360139440339865 10217121206520104580254899)
          ·
            refine ⟨15325681809780156870382349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10217121206520104580254899 15325681809780156870382349)
            ·
              refine ⟨5747130678667558826393381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15325681809780156870382349 5747130678667558826393381)
              ·
                refine ⟨1077587002250167279948759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5747130678667558826393381 1077587002250167279948759)
                ·
                  refine ⟨1616380503375250919923139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1077587002250167279948759 1616380503375250919923139)
                  ·
                    refine ⟨2424570755062876379884709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1616380503375250919923139 2424570755062876379884709)
                    ·
                      refine ⟨454607016574289321228383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2424570755062876379884709 454607016574289321228383)
                      ·
                        rfl

theorem cell23_885344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 4].length) (baseStart_885344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_885344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_885344 prefixEnd_885344 := by exact prefixLift 885344
  have htrace : WordTrace (prefixWord ++ tailWord_885344) baseStart_885344 baseEnd_885344 := by
    simpa [prefixWord, tailWord_885344, baseEnd_885344] using wordTrace_append hprefix tailTrace_885344
  have hstable : (prefixWord ++ tailWord_885344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885344).length < 2 ^ (prefixWord ++ tailWord_885344).sum := by decide
  have hdescent : baseEnd_885344 < baseStart_885344 := by decide
  rcases family_descends (prefixWord ++ tailWord_885344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885347 : List Nat := [1, 1, 1, 5, 1, 2, 1, 2, 3, 1, 5]
def baseStart_885347 : Nat := 118140960795 + 885347 * 2 ^ 59
def prefixEnd_885347 : Nat := 4983230072969 + 3 ^ 40 * 885347 * 2
def baseEnd_885347 : Nat := 454608557016252809490869

theorem tailTrace_885347 : CollatzResearch.WordTrace tailWord_885347 prefixEnd_885347 454608557016252809490869 := by
  unfold tailWord_885347
  simp only [CollatzResearch.WordTrace]
  refine ⟨32291257923546499074646295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21527505282364332716430863 32291257923546499074646295)
  ·
    refine ⟨48436886885319748611969443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32291257923546499074646295 48436886885319748611969443)
    ·
      refine ⟨72655330327979622917954165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48436886885319748611969443 72655330327979622917954165)
      ·
        refine ⟨6811437218248089648558203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72655330327979622917954165 6811437218248089648558203)
        ·
          refine ⟨10217155827372134472837305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6811437218248089648558203 10217155827372134472837305)
          ·
            refine ⟨7662866870529100854627979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10217155827372134472837305 7662866870529100854627979)
            ·
              refine ⟨11494300305793651281941969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7662866870529100854627979 11494300305793651281941969)
              ·
                refine ⟨8620725229345238461456477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11494300305793651281941969 8620725229345238461456477)
                ·
                  refine ⟨3232771961004464423046179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8620725229345238461456477 3232771961004464423046179)
                  ·
                    refine ⟨4849157941506696634569269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3232771961004464423046179 4849157941506696634569269)
                    ·
                      refine ⟨454608557016252809490869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4849157941506696634569269 454608557016252809490869)
                      ·
                        rfl

theorem cell23_885347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_885347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_885347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_885347 prefixEnd_885347 := by exact prefixLift 885347
  have htrace : WordTrace (prefixWord ++ tailWord_885347) baseStart_885347 baseEnd_885347 := by
    simpa [prefixWord, tailWord_885347, baseEnd_885347] using wordTrace_append hprefix tailTrace_885347
  have hstable : (prefixWord ++ tailWord_885347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885347).length < 2 ^ (prefixWord ++ tailWord_885347).sum := by decide
  have hdescent : baseEnd_885347 < baseStart_885347 := by decide
  rcases family_descends (prefixWord ++ tailWord_885347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885354 : List Nat := [3, 1, 3, 2, 1, 1, 1, 1, 6, 4]
def baseStart_885354 : Nat := 118140960795 + 885354 * 2 ^ 59
def prefixEnd_885354 : Nat := 4983230072969 + 3 ^ 40 * 885354 * 2
def baseEnd_885354 : Nat := 151537383793611427367779

theorem tailTrace_885354 : CollatzResearch.WordTrace tailWord_885354 prefixEnd_885354 151537383793611427367779 := by
  unfold tailWord_885354
  simp only [CollatzResearch.WordTrace]
  refine ⟨8072878308630284817537779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21527675489680759513434077 8072878308630284817537779)
  ·
    refine ⟨12109317462945427226306669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8072878308630284817537779 12109317462945427226306669)
    ·
      refine ⟨4540994048604535209865001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12109317462945427226306669 4540994048604535209865001)
      ·
        refine ⟨3405745536453401407398751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4540994048604535209865001 3405745536453401407398751)
        ·
          refine ⟨5108618304680102111098127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3405745536453401407398751 5108618304680102111098127)
          ·
            refine ⟨7662927457020153166647191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5108618304680102111098127 7662927457020153166647191)
            ·
              refine ⟨11494391185530229749970787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7662927457020153166647191 11494391185530229749970787)
              ·
                refine ⟨17241586778295344624956181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11494391185530229749970787 17241586778295344624956181)
                ·
                  refine ⟨808199380232594279294821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 17241586778295344624956181 808199380232594279294821)
                  ·
                    refine ⟨151537383793611427367779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 808199380232594279294821 151537383793611427367779)
                    ·
                      rfl

theorem cell23_885354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_885354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_885354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_885354 prefixEnd_885354 := by exact prefixLift 885354
  have htrace : WordTrace (prefixWord ++ tailWord_885354) baseStart_885354 baseEnd_885354 := by
    simpa [prefixWord, tailWord_885354, baseEnd_885354] using wordTrace_append hprefix tailTrace_885354
  have hstable : (prefixWord ++ tailWord_885354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885354).length < 2 ^ (prefixWord ++ tailWord_885354).sum := by decide
  have hdescent : baseEnd_885354 < baseStart_885354 := by decide
  rcases family_descends (prefixWord ++ tailWord_885354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885415 : List Nat := [1, 1, 6, 3, 2, 1, 1, 1, 1, 1, 5]
def baseStart_885415 : Nat := 118140960795 + 885415 * 2 ^ 59
def prefixEnd_885415 : Nat := 4983230072969 + 3 ^ 40 * 885415 * 2
def baseEnd_885415 : Nat := 454643473700758543440557

theorem tailTrace_885415 : CollatzResearch.WordTrace tailWord_885415 prefixEnd_885415 454643473700758543440557 := by
  unfold tailWord_885415
  simp only [CollatzResearch.WordTrace]
  refine ⟨32293738087300146688121699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21529158724866764458747799 32293738087300146688121699)
  ·
    refine ⟨48440607130950220032182549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32293738087300146688121699 48440607130950220032182549)
    ·
      refine ⟨2270653459263291564008557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 48440607130950220032182549 2270653459263291564008557)
      ·
        refine ⟨851495047223734336503209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2270653459263291564008557 851495047223734336503209)
        ·
          refine ⟨638621285417800752377407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 851495047223734336503209 638621285417800752377407)
          ·
            refine ⟨957931928126701128566111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 638621285417800752377407 957931928126701128566111)
            ·
              refine ⟨1436897892190051692849167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 957931928126701128566111 1436897892190051692849167)
              ·
                refine ⟨2155346838285077539273751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1436897892190051692849167 2155346838285077539273751)
                ·
                  refine ⟨3233020257427616308910627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2155346838285077539273751 3233020257427616308910627)
                  ·
                    refine ⟨4849530386141424463365941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3233020257427616308910627 4849530386141424463365941)
                    ·
                      refine ⟨454643473700758543440557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4849530386141424463365941 454643473700758543440557)
                      ·
                        rfl

theorem cell23_885415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_885415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_885415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_885415 prefixEnd_885415 := by exact prefixLift 885415
  have htrace : WordTrace (prefixWord ++ tailWord_885415) baseStart_885415 baseEnd_885415 := by
    simpa [prefixWord, tailWord_885415, baseEnd_885415] using wordTrace_append hprefix tailTrace_885415
  have hstable : (prefixWord ++ tailWord_885415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885415).length < 2 ^ (prefixWord ++ tailWord_885415).sum := by decide
  have hdescent : baseEnd_885415 < baseStart_885415 := by decide
  rcases family_descends (prefixWord ++ tailWord_885415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885417 : List Nat := [1, 2, 1, 1, 1, 1, 2, 4, 1, 5, 4]
def baseStart_885417 : Nat := 118140960795 + 885417 * 2 ^ 59
def prefixEnd_885417 : Nat := 4983230072969 + 3 ^ 40 * 885417 * 2
def baseEnd_885417 : Nat := 454644500662067535615547

theorem tailTrace_885417 : CollatzResearch.WordTrace tailWord_885417 prefixEnd_885417 454644500662067535615547 := by
  unfold tailWord_885417
  simp only [CollatzResearch.WordTrace]
  refine ⟨32293811033292901029694505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21529207355528600686463003 32293811033292901029694505)
  ·
    refine ⟨24220358274969675772270879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32293811033292901029694505 24220358274969675772270879)
    ·
      refine ⟨36330537412454513658406319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24220358274969675772270879 36330537412454513658406319)
      ·
        refine ⟨54495806118681770487609479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36330537412454513658406319 54495806118681770487609479)
        ·
          refine ⟨81743709178022655731414219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54495806118681770487609479 81743709178022655731414219)
          ·
            refine ⟨122615563767033983597121329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81743709178022655731414219 122615563767033983597121329)
            ·
              refine ⟨91961672825275487697840997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122615563767033983597121329 91961672825275487697840997)
              ·
                refine ⟨17242813654739153943345187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91961672825275487697840997 17242813654739153943345187)
                ·
                  refine ⟨25864220482108730915017781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17242813654739153943345187 25864220482108730915017781)
                  ·
                    refine ⟨2424770670197693523282917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25864220482108730915017781 2424770670197693523282917)
                    ·
                      refine ⟨454644500662067535615547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2424770670197693523282917 454644500662067535615547)
                      ·
                        rfl

theorem cell23_885417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 5, 4].length) (baseStart_885417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_885417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_885417 prefixEnd_885417 := by exact prefixLift 885417
  have htrace : WordTrace (prefixWord ++ tailWord_885417) baseStart_885417 baseEnd_885417 := by
    simpa [prefixWord, tailWord_885417, baseEnd_885417] using wordTrace_append hprefix tailTrace_885417
  have hstable : (prefixWord ++ tailWord_885417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885417).length < 2 ^ (prefixWord ++ tailWord_885417).sum := by decide
  have hdescent : baseEnd_885417 < baseStart_885417 := by decide
  rcases family_descends (prefixWord ++ tailWord_885417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885429 : List Nat := [1, 3, 3, 3, 1, 3, 2, 2, 1, 2, 2]
def baseStart_885429 : Nat := 118140960795 + 885429 * 2 ^ 59
def prefixEnd_885429 : Nat := 4983230072969 + 3 ^ 40 * 885429 * 2
def baseEnd_885429 : Nat := 454650662429921488665493

theorem tailTrace_885429 : CollatzResearch.WordTrace tailWord_885429 prefixEnd_885429 454650662429921488665493 := by
  unfold tailWord_885429
  simp only [CollatzResearch.WordTrace]
  refine ⟨32294248709249427079131341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21529499139499618052754227 32294248709249427079131341)
  ·
    refine ⟨12110343265968535154674253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32294248709249427079131341 12110343265968535154674253)
    ·
      refine ⟨4541378724738200683002845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12110343265968535154674253 4541378724738200683002845)
      ·
        refine ⟨1703017021776825256126067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4541378724738200683002845 1703017021776825256126067)
        ·
          refine ⟨2554525532665237884189101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1703017021776825256126067 2554525532665237884189101)
          ·
            refine ⟨957947074749464206570913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2554525532665237884189101 957947074749464206570913)
            ·
              refine ⟨718460306062098154928185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 957947074749464206570913 718460306062098154928185)
              ·
                refine ⟨538845229546573616196139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 718460306062098154928185 538845229546573616196139)
                ·
                  refine ⟨808267844319860424294209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 538845229546573616196139 808267844319860424294209)
                  ·
                    refine ⟨606200883239895318220657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 808267844319860424294209 606200883239895318220657)
                    ·
                      refine ⟨454650662429921488665493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 606200883239895318220657 454650662429921488665493)
                      ·
                        rfl

theorem cell23_885429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_885429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_885429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_885429 prefixEnd_885429 := by exact prefixLift 885429
  have htrace : WordTrace (prefixWord ++ tailWord_885429) baseStart_885429 baseEnd_885429 := by
    simpa [prefixWord, tailWord_885429, baseEnd_885429] using wordTrace_append hprefix tailTrace_885429
  have hstable : (prefixWord ++ tailWord_885429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885429).length < 2 ^ (prefixWord ++ tailWord_885429).sum := by decide
  have hdescent : baseEnd_885429 < baseStart_885429 := by decide
  rcases family_descends (prefixWord ++ tailWord_885429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885444 : List Nat := [2, 3, 3, 1, 1, 2, 1, 1, 1, 8]
def baseStart_885444 : Nat := 118140960795 + 885444 * 2 ^ 59
def prefixEnd_885444 : Nat := 4983230072969 + 3 ^ 40 * 885444 * 2
def baseEnd_885444 : Nat := 151552788213246309992641

theorem tailTrace_885444 : CollatzResearch.WordTrace tailWord_885444 prefixEnd_885444 151552788213246309992641 := by
  unfold tailWord_885444
  simp only [CollatzResearch.WordTrace]
  refine ⟨16147397902097542320463693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21529863869463389760618257 16147397902097542320463693)
  ·
    refine ⟨6055274213286578370173885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16147397902097542320463693 6055274213286578370173885)
    ·
      refine ⟨2270727829982466888815207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6055274213286578370173885 2270727829982466888815207)
      ·
        refine ⟨3406091744973700333222811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2270727829982466888815207 3406091744973700333222811)
        ·
          refine ⟨5109137617460550499834217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3406091744973700333222811 5109137617460550499834217)
          ·
            refine ⟨3831853213095412874875663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5109137617460550499834217 3831853213095412874875663)
            ·
              refine ⟨5747779819643119312313495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3831853213095412874875663 5747779819643119312313495)
              ·
                refine ⟨8621669729464678968470243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5747779819643119312313495 8621669729464678968470243)
                ·
                  refine ⟨12932504594197018452705365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8621669729464678968470243 12932504594197018452705365)
                  ·
                    refine ⟨151552788213246309992641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 12932504594197018452705365 151552788213246309992641)
                    ·
                      rfl

theorem cell23_885444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_885444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_885444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_885444 prefixEnd_885444 := by exact prefixLift 885444
  have htrace : WordTrace (prefixWord ++ tailWord_885444) baseStart_885444 baseEnd_885444 := by
    simpa [prefixWord, tailWord_885444, baseEnd_885444] using wordTrace_append hprefix tailTrace_885444
  have hstable : (prefixWord ++ tailWord_885444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885444).length < 2 ^ (prefixWord ++ tailWord_885444).sum := by decide
  have hdescent : baseEnd_885444 < baseStart_885444 := by decide
  rcases family_descends (prefixWord ++ tailWord_885444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885451 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 8, 2, 2]
def baseStart_885451 : Nat := 118140960795 + 885451 * 2 ^ 59
def prefixEnd_885451 : Nat := 4983230072969 + 3 ^ 40 * 885451 * 2
def baseEnd_885451 : Nat := 454661959004320402590391

theorem tailTrace_885451 : CollatzResearch.WordTrace tailWord_885451 prefixEnd_885451 454661959004320402590391 := by
  unfold tailWord_885451
  simp only [CollatzResearch.WordTrace]
  refine ⟨32295051115169724836432207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21530034076779816557621471 32295051115169724836432207)
  ·
    refine ⟨48442576672754587254648311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32295051115169724836432207 48442576672754587254648311)
    ·
      refine ⟨72663865009131880881972467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48442576672754587254648311 72663865009131880881972467)
      ·
        refine ⟨108995797513697821322958701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72663865009131880881972467 108995797513697821322958701)
        ·
          refine ⟨40873424067636682996109513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108995797513697821322958701 40873424067636682996109513)
          ·
            refine ⟨30655068050727512247082135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40873424067636682996109513 30655068050727512247082135)
            ·
              refine ⟨45982602076091268370623203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30655068050727512247082135 45982602076091268370623203)
              ·
                refine ⟨68973903114136902555934805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45982602076091268370623203 68973903114136902555934805)
                ·
                  refine ⟨808287927118791826827361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 68973903114136902555934805 808287927118791826827361)
                  ·
                    refine ⟨606215945339093870120521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 808287927118791826827361 606215945339093870120521)
                    ·
                      refine ⟨454661959004320402590391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 606215945339093870120521 454661959004320402590391)
                      ·
                        rfl

theorem cell23_885451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 8, 2, 2].length) (baseStart_885451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_885451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_885451 prefixEnd_885451 := by exact prefixLift 885451
  have htrace : WordTrace (prefixWord ++ tailWord_885451) baseStart_885451 baseEnd_885451 := by
    simpa [prefixWord, tailWord_885451, baseEnd_885451] using wordTrace_append hprefix tailTrace_885451
  have hstable : (prefixWord ++ tailWord_885451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885451).length < 2 ^ (prefixWord ++ tailWord_885451).sum := by decide
  have hdescent : baseEnd_885451 < baseStart_885451 := by decide
  rcases family_descends (prefixWord ++ tailWord_885451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885541 : List Nat := [1, 3, 1, 2, 3, 1, 3, 2, 2, 1, 4]
def baseStart_885541 : Nat := 118140960795 + 885541 * 2 ^ 59
def prefixEnd_885541 : Nat := 4983230072969 + 3 ^ 40 * 885541 * 2
def baseEnd_885541 : Nat := 454708172263225050464977

theorem tailTrace_885541 : CollatzResearch.WordTrace tailWord_885541 prefixEnd_885541 454708172263225050464977 := by
  unfold tailWord_885541
  simp only [CollatzResearch.WordTrace]
  refine ⟨32298333684843670207208477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21532222456562446804805651 32298333684843670207208477)
  ·
    refine ⟨12111875131816376327703179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32298333684843670207208477 12111875131816376327703179)
    ·
      refine ⟨18167812697724564491554769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12111875131816376327703179 18167812697724564491554769)
      ·
        refine ⟨13625859523293423368666077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18167812697724564491554769 13625859523293423368666077)
        ·
          refine ⟨5109697321235033763249779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13625859523293423368666077 5109697321235033763249779)
          ·
            refine ⟨7664545981852550644874669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5109697321235033763249779 7664545981852550644874669)
            ·
              refine ⟨2874204743194706491828001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7664545981852550644874669 2874204743194706491828001)
              ·
                refine ⟨2155653557396029868871001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2874204743194706491828001 2155653557396029868871001)
                ·
                  refine ⟨1616740168047022401653251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2155653557396029868871001 1616740168047022401653251)
                  ·
                    refine ⟨2425110252070533602479877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1616740168047022401653251 2425110252070533602479877)
                    ·
                      refine ⟨454708172263225050464977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2425110252070533602479877 454708172263225050464977)
                      ·
                        rfl

theorem cell23_885541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 2, 2, 1, 4].length) (baseStart_885541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_885541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_885541 prefixEnd_885541 := by exact prefixLift 885541
  have htrace : WordTrace (prefixWord ++ tailWord_885541) baseStart_885541 baseEnd_885541 := by
    simpa [prefixWord, tailWord_885541, baseEnd_885541] using wordTrace_append hprefix tailTrace_885541
  have hstable : (prefixWord ++ tailWord_885541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885541).length < 2 ^ (prefixWord ++ tailWord_885541).sum := by decide
  have hdescent : baseEnd_885541 < baseStart_885541 := by decide
  rcases family_descends (prefixWord ++ tailWord_885541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885602 : List Nat := [3, 3, 2, 1, 3, 1, 1, 4, 1, 4]
def baseStart_885602 : Nat := 118140960795 + 885602 * 2 ^ 59
def prefixEnd_885602 : Nat := 4983230072969 + 3 ^ 40 * 885602 * 2
def baseEnd_885602 : Nat := 151579831527716437267399

theorem tailTrace_885602 : CollatzResearch.WordTrace tailWord_885602 prefixEnd_885602 151579831527716437267399 := by
  unfold tailWord_885602
  simp only [CollatzResearch.WordTrace]
  refine ⟨8075139634405669406294765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21533705691748451750119373 8075139634405669406294765)
  ·
    refine ⟨3028177362902126027360537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8075139634405669406294765 3028177362902126027360537)
    ·
      refine ⟨2271133022176594520520403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3028177362902126027360537 2271133022176594520520403)
      ·
        refine ⟨3406699533264891780780605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2271133022176594520520403 3406699533264891780780605)
        ·
          refine ⟨1277512324974334417792727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3406699533264891780780605 1277512324974334417792727)
          ·
            refine ⟨1916268487461501626689091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1277512324974334417792727 1916268487461501626689091)
            ·
              refine ⟨2874402731192252440033637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1916268487461501626689091 2874402731192252440033637)
              ·
                refine ⟨538950512098547332506307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2874402731192252440033637 538950512098547332506307)
                ·
                  refine ⟨808425768147820998759461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 538950512098547332506307 808425768147820998759461)
                  ·
                    refine ⟨151579831527716437267399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 808425768147820998759461 151579831527716437267399)
                    ·
                      rfl

theorem cell23_885602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_885602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_885602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_885602 prefixEnd_885602 := by exact prefixLift 885602
  have htrace : WordTrace (prefixWord ++ tailWord_885602) baseStart_885602 baseEnd_885602 := by
    simpa [prefixWord, tailWord_885602, baseEnd_885602] using wordTrace_append hprefix tailTrace_885602
  have hstable : (prefixWord ++ tailWord_885602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885602).length < 2 ^ (prefixWord ++ tailWord_885602).sum := by decide
  have hdescent : baseEnd_885602 < baseStart_885602 := by decide
  rcases family_descends (prefixWord ++ tailWord_885602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885618 : List Nat := [3, 2, 1, 2, 1, 1, 2, 2, 4, 3, 2]
def baseStart_885618 : Nat := 118140960795 + 885618 * 2 ^ 59
def prefixEnd_885618 : Nat := 4983230072969 + 3 ^ 40 * 885618 * 2
def baseEnd_885618 : Nat := 454747710273621249202123

theorem tailTrace_885618 : CollatzResearch.WordTrace tailWord_885618 prefixEnd_885618 454747710273621249202123 := by
  unfold tailWord_885618
  simp only [CollatzResearch.WordTrace]
  refine ⟨8075285526391178089440377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21534094737043141571841005 8075285526391178089440377)
  ·
    refine ⟨6056464144793383567080283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8075285526391178089440377 6056464144793383567080283)
    ·
      refine ⟨9084696217190075350620425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6056464144793383567080283 9084696217190075350620425)
      ·
        refine ⟨6813522162892556512965319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9084696217190075350620425 6813522162892556512965319)
        ·
          refine ⟨10220283244338834769447979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6813522162892556512965319 10220283244338834769447979)
          ·
            refine ⟨15330424866508252154171969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10220283244338834769447979 15330424866508252154171969)
            ·
              refine ⟨11497818649881189115628977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15330424866508252154171969 11497818649881189115628977)
              ·
                refine ⟨8623363987410891836721733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11497818649881189115628977 8623363987410891836721733)
                ·
                  refine ⟨1616880747639542219385325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8623363987410891836721733 1616880747639542219385325)
                  ·
                    refine ⟨606330280364828332269497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1616880747639542219385325 606330280364828332269497)
                    ·
                      refine ⟨454747710273621249202123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 606330280364828332269497 454747710273621249202123)
                      ·
                        rfl

theorem cell23_885618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 4, 3, 2].length) (baseStart_885618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_885618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_885618 prefixEnd_885618 := by exact prefixLift 885618
  have htrace : WordTrace (prefixWord ++ tailWord_885618) baseStart_885618 baseEnd_885618 := by
    simpa [prefixWord, tailWord_885618, baseEnd_885618] using wordTrace_append hprefix tailTrace_885618
  have hstable : (prefixWord ++ tailWord_885618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885618).length < 2 ^ (prefixWord ++ tailWord_885618).sum := by decide
  have hdescent : baseEnd_885618 < baseStart_885618 := by decide
  rcases family_descends (prefixWord ++ tailWord_885618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885631 : List Nat := [1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 4]
def baseStart_885631 : Nat := 118140960795 + 885631 * 2 ^ 59
def prefixEnd_885631 : Nat := 4983230072969 + 3 ^ 40 * 885631 * 2
def baseEnd_885631 : Nat := 454754385522129698339563

theorem tailTrace_885631 : CollatzResearch.WordTrace tailWord_885631 prefixEnd_885631 454754385522129698339563 := by
  unfold tailWord_885631
  simp only [CollatzResearch.WordTrace]
  refine ⟨32301616254517615577984747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21534410836345077051989831 32301616254517615577984747)
  ·
    refine ⟨48452424381776423366977121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32301616254517615577984747 48452424381776423366977121)
    ·
      refine ⟨36339318286332317525232841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48452424381776423366977121 36339318286332317525232841)
      ·
        refine ⟨27254488714749238143924631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36339318286332317525232841 27254488714749238143924631)
        ·
          refine ⟨40881733072123857215886947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27254488714749238143924631 40881733072123857215886947)
          ·
            refine ⟨61322599608185785823830421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40881733072123857215886947 61322599608185785823830421)
            ·
              refine ⟨2874496856633708710492051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 61322599608185785823830421 2874496856633708710492051)
              ·
                refine ⟨4311745284950563065738077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2874496856633708710492051 4311745284950563065738077)
                ·
                  refine ⟨1616904481856461149651779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4311745284950563065738077 1616904481856461149651779)
                  ·
                    refine ⟨2425356722784691724477669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1616904481856461149651779 2425356722784691724477669)
                    ·
                      refine ⟨454754385522129698339563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2425356722784691724477669 454754385522129698339563)
                      ·
                        rfl

theorem cell23_885631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 4].length) (baseStart_885631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_885631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_885631 prefixEnd_885631 := by exact prefixLift 885631
  have htrace : WordTrace (prefixWord ++ tailWord_885631) baseStart_885631 baseEnd_885631 := by
    simpa [prefixWord, tailWord_885631, baseEnd_885631] using wordTrace_append hprefix tailTrace_885631
  have hstable : (prefixWord ++ tailWord_885631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885631).length < 2 ^ (prefixWord ++ tailWord_885631).sum := by decide
  have hdescent : baseEnd_885631 < baseStart_885631 := by decide
  rcases family_descends (prefixWord ++ tailWord_885631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885641 : List Nat := [1, 2, 1, 1, 5, 2, 2, 2, 1, 6]
def baseStart_885641 : Nat := 118140960795 + 885641 * 2 ^ 59
def prefixEnd_885641 : Nat := 4983230072969 + 3 ^ 40 * 885641 * 2
def baseEnd_885641 : Nat := 151586506776224886404839

theorem tailTrace_885641 : CollatzResearch.WordTrace tailWord_885641 prefixEnd_885641 151586506776224886404839 := by
  unfold tailWord_885641
  simp only [CollatzResearch.WordTrace]
  refine ⟨32301980984481387285848777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21534653989654258190565851 32301980984481387285848777)
  ·
    refine ⟨24226485738361040464386583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32301980984481387285848777 24226485738361040464386583)
    ·
      refine ⟨36339728607541560696579875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24226485738361040464386583 36339728607541560696579875)
      ·
        refine ⟨54509592911312341044869813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36339728607541560696579875 54509592911312341044869813)
        ·
          refine ⟨5110274335435531972956545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54509592911312341044869813 5110274335435531972956545)
          ·
            refine ⟨3832705751576648979717409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5110274335435531972956545 3832705751576648979717409)
            ·
              refine ⟨2874529313682486734788057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3832705751576648979717409 2874529313682486734788057)
              ·
                refine ⟨2155896985261865051091043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2874529313682486734788057 2155896985261865051091043)
                ·
                  refine ⟨3233845477892797576636565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2155896985261865051091043 3233845477892797576636565)
                  ·
                    refine ⟨151586506776224886404839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3233845477892797576636565 151586506776224886404839)
                    ·
                      rfl

theorem cell23_885641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 2, 1, 6].length) (baseStart_885641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_885641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_885641 prefixEnd_885641 := by exact prefixLift 885641
  have htrace : WordTrace (prefixWord ++ tailWord_885641) baseStart_885641 baseEnd_885641 := by
    simpa [prefixWord, tailWord_885641, baseEnd_885641] using wordTrace_append hprefix tailTrace_885641
  have hstable : (prefixWord ++ tailWord_885641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885641).length < 2 ^ (prefixWord ++ tailWord_885641).sum := by decide
  have hdescent : baseEnd_885641 < baseStart_885641 := by decide
  rcases family_descends (prefixWord ++ tailWord_885641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885642 : List Nat := [3, 1, 2, 4, 1, 1, 1, 5, 1, 1, 3]
def baseStart_885642 : Nat := 118140960795 + 885642 * 2 ^ 59
def prefixEnd_885642 : Nat := 4983230072969 + 3 ^ 40 * 885642 * 2
def baseEnd_885642 : Nat := 454760033809329155302013

theorem tailTrace_885642 : CollatzResearch.WordTrace tailWord_885642 prefixEnd_885642 454760033809329155302013 := by
  unfold tailWord_885642
  simp only [CollatzResearch.WordTrace]
  refine ⟨8075504364369441114158795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21534678304985176304423453 8075504364369441114158795)
  ·
    refine ⟨12113256546554161671238193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8075504364369441114158795 12113256546554161671238193)
    ·
      refine ⟨9084942409915621253428645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12113256546554161671238193 9084942409915621253428645)
      ·
        refine ⟨1703426701859178985017871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9084942409915621253428645 1703426701859178985017871)
        ·
          refine ⟨2555140052788768477526807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1703426701859178985017871 2555140052788768477526807)
          ·
            refine ⟨3832710079183152716290211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2555140052788768477526807 3832710079183152716290211)
            ·
              refine ⟨5749065118774729074435317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3832710079183152716290211 5749065118774729074435317)
              ·
                refine ⟨538974854885130850728311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5749065118774729074435317 538974854885130850728311)
                ·
                  refine ⟨808462282327696276092467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 538974854885130850728311 808462282327696276092467)
                  ·
                    refine ⟨1212693423491544414138701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 808462282327696276092467 1212693423491544414138701)
                    ·
                      refine ⟨454760033809329155302013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1212693423491544414138701 454760033809329155302013)
                      ·
                        rfl

theorem cell23_885642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_885642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_885642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_885642 prefixEnd_885642 := by exact prefixLift 885642
  have htrace : WordTrace (prefixWord ++ tailWord_885642) baseStart_885642 baseEnd_885642 := by
    simpa [prefixWord, tailWord_885642, baseEnd_885642] using wordTrace_append hprefix tailTrace_885642
  have hstable : (prefixWord ++ tailWord_885642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885642).length < 2 ^ (prefixWord ++ tailWord_885642).sum := by decide
  have hdescent : baseEnd_885642 < baseStart_885642 := by decide
  rcases family_descends (prefixWord ++ tailWord_885642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885651 : List Nat := [1, 1, 1, 2, 1, 2, 1, 4, 5, 2, 3]
def baseStart_885651 : Nat := 118140960795 + 885651 * 2 ^ 59
def prefixEnd_885651 : Nat := 4983230072969 + 3 ^ 40 * 885651 * 2
def baseEnd_885651 : Nat := 454764655135219620089471

theorem tailTrace_885651 : CollatzResearch.WordTrace tailWord_885651 prefixEnd_885651 454764655135219620089471 := by
  unfold tailWord_885651
  simp only [CollatzResearch.WordTrace]
  refine ⟨32302345714445158993712807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21534897142963439329141871 32302345714445158993712807)
  ·
    refine ⟨48453518571667738490569211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32302345714445158993712807 48453518571667738490569211)
    ·
      refine ⟨72680277857501607735853817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48453518571667738490569211 72680277857501607735853817)
      ·
        refine ⟨54510208393126205801890363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72680277857501607735853817 54510208393126205801890363)
        ·
          refine ⟨81765312589689308702835545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54510208393126205801890363 81765312589689308702835545)
          ·
            refine ⟨61323984442266981527126659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81765312589689308702835545 61323984442266981527126659)
            ·
              refine ⟨91985976663400472290689989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61323984442266981527126659 91985976663400472290689989)
              ·
                refine ⟨17247370624387588554504373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91985976663400472290689989 17247370624387588554504373)
                ·
                  refine ⟨1616940996036336426984785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17247370624387588554504373 1616940996036336426984785)
                  ·
                    refine ⟨1212705747027252320238589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1616940996036336426984785 1212705747027252320238589)
                    ·
                      refine ⟨454764655135219620089471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1212705747027252320238589 454764655135219620089471)
                      ·
                        rfl

theorem cell23_885651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 5, 2, 3].length) (baseStart_885651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_885651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_885651 prefixEnd_885651 := by exact prefixLift 885651
  have htrace : WordTrace (prefixWord ++ tailWord_885651) baseStart_885651 baseEnd_885651 := by
    simpa [prefixWord, tailWord_885651, baseEnd_885651] using wordTrace_append hprefix tailTrace_885651
  have hstable : (prefixWord ++ tailWord_885651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885651).length < 2 ^ (prefixWord ++ tailWord_885651).sum := by decide
  have hdescent : baseEnd_885651 < baseStart_885651 := by decide
  rcases family_descends (prefixWord ++ tailWord_885651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885661 : List Nat := [1, 4, 2, 1, 2, 1, 2, 2, 1, 1, 6]
def baseStart_885661 : Nat := 118140960795 + 885661 * 2 ^ 59
def prefixEnd_885661 : Nat := 4983230072969 + 3 ^ 40 * 885661 * 2
def baseEnd_885661 : Nat := 454769789941764580964425

theorem tailTrace_885661 : CollatzResearch.WordTrace tailWord_885661 prefixEnd_885661 454769789941764580964425 := by
  unfold tailWord_885661
  simp only [CollatzResearch.WordTrace]
  refine ⟨32302710444408930701576837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21535140296272620467717891 32302710444408930701576837)
  ·
    refine ⟨6056758208326674506545657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32302710444408930701576837 6056758208326674506545657)
    ·
      refine ⟨4542568656245005879909243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6056758208326674506545657 4542568656245005879909243)
      ·
        refine ⟨6813852984367508819863865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4542568656245005879909243 6813852984367508819863865)
        ·
          refine ⟨5110389738275631614897899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6813852984367508819863865 5110389738275631614897899)
          ·
            refine ⟨7665584607413447422346849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5110389738275631614897899 7665584607413447422346849)
            ·
              refine ⟨5749188455560085566760137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7665584607413447422346849 5749188455560085566760137)
              ·
                refine ⟨4311891341670064175070103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5749188455560085566760137 4311891341670064175070103)
                ·
                  refine ⟨6467837012505096262605155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4311891341670064175070103 6467837012505096262605155)
                  ·
                    refine ⟨9701755518757644393907733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6467837012505096262605155 9701755518757644393907733)
                    ·
                      refine ⟨454769789941764580964425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9701755518757644393907733 454769789941764580964425)
                      ·
                        rfl

theorem cell23_885661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_885661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_885661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_885661 prefixEnd_885661 := by exact prefixLift 885661
  have htrace : WordTrace (prefixWord ++ tailWord_885661) baseStart_885661 baseEnd_885661 := by
    simpa [prefixWord, tailWord_885661, baseEnd_885661] using wordTrace_append hprefix tailTrace_885661
  have hstable : (prefixWord ++ tailWord_885661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885661).length < 2 ^ (prefixWord ++ tailWord_885661).sum := by decide
  have hdescent : baseEnd_885661 < baseStart_885661 := by decide
  rcases family_descends (prefixWord ++ tailWord_885661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885685 : List Nat := [1, 3, 3, 2, 1, 1, 4, 2, 1, 2, 3]
def baseStart_885685 : Nat := 118140960795 + 885685 * 2 ^ 59
def prefixEnd_885685 : Nat := 4983230072969 + 3 ^ 40 * 885685 * 2
def baseEnd_885685 : Nat := 454782113477472487064315

theorem tailTrace_885685 : CollatzResearch.WordTrace tailWord_885685 prefixEnd_885685 454782113477472487064315 := by
  unfold tailWord_885685
  simp only [CollatzResearch.WordTrace]
  refine ⟨32303585796321982800450509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21535723864214655200300339 32303585796321982800450509)
  ·
    refine ⟨12113844673620743550168941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32303585796321982800450509 12113844673620743550168941)
    ·
      refine ⟨4542691752607778831313353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12113844673620743550168941 4542691752607778831313353)
      ·
        refine ⟨3407018814455834123485015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4542691752607778831313353 3407018814455834123485015)
        ·
          refine ⟨5110528221683751185227523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3407018814455834123485015 5110528221683751185227523)
          ·
            refine ⟨7665792332525626777841285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5110528221683751185227523 7665792332525626777841285)
            ·
              refine ⟨1437336062348555020845241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7665792332525626777841285 1437336062348555020845241)
              ·
                refine ⟨1078002046761416265633931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1437336062348555020845241 1078002046761416265633931)
                ·
                  refine ⟨1617003070142124398450897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1078002046761416265633931 1617003070142124398450897)
                  ·
                    refine ⟨1212752302606593298838173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1617003070142124398450897 1212752302606593298838173)
                    ·
                      refine ⟨454782113477472487064315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1212752302606593298838173 454782113477472487064315)
                      ·
                        rfl

theorem cell23_885685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_885685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_885685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_885685 prefixEnd_885685 := by exact prefixLift 885685
  have htrace : WordTrace (prefixWord ++ tailWord_885685) baseStart_885685 baseEnd_885685 := by
    simpa [prefixWord, tailWord_885685, baseEnd_885685] using wordTrace_append hprefix tailTrace_885685
  have hstable : (prefixWord ++ tailWord_885685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885685).length < 2 ^ (prefixWord ++ tailWord_885685).sum := by decide
  have hdescent : baseEnd_885685 < baseStart_885685 := by decide
  rcases family_descends (prefixWord ++ tailWord_885685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885688 : List Nat := [2, 1, 2, 1, 2, 6, 2, 7]
def baseStart_885688 : Nat := 118140960795 + 885688 * 2 ^ 59
def prefixEnd_885688 : Nat := 4983230072969 + 3 ^ 40 * 885688 * 2
def baseEnd_885688 : Nat := 16843839034053184271363

theorem tailTrace_885688 : CollatzResearch.WordTrace tailWord_885688 prefixEnd_885688 16843839034053184271363 := by
  unfold tailWord_885688
  simp only [CollatzResearch.WordTrace]
  refine ⟨16151847607655557156404859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21535796810207409541873145 16151847607655557156404859)
  ·
    refine ⟨24227771411483335734607289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16151847607655557156404859 24227771411483335734607289)
    ·
      refine ⟨18170828558612501800955467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24227771411483335734607289 18170828558612501800955467)
      ·
        refine ⟨27256242837918752701433201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18170828558612501800955467 27256242837918752701433201)
        ·
          refine ⟨20442182128439064526074901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27256242837918752701433201 20442182128439064526074901)
          ·
            refine ⟨958227287270581149659761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 20442182128439064526074901 958227287270581149659761)
            ·
              refine ⟨718670465452935862244821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 958227287270581149659761 718670465452935862244821)
              ·
                refine ⟨16843839034053184271363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 718670465452935862244821 16843839034053184271363)
                ·
                  rfl

theorem cell23_885688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 2, 7].length) (baseStart_885688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_885688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_885688 prefixEnd_885688 := by exact prefixLift 885688
  have htrace : WordTrace (prefixWord ++ tailWord_885688) baseStart_885688 baseEnd_885688 := by
    simpa [prefixWord, tailWord_885688, baseEnd_885688] using wordTrace_append hprefix tailTrace_885688
  have hstable : (prefixWord ++ tailWord_885688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885688).length < 2 ^ (prefixWord ++ tailWord_885688).sum := by decide
  have hdescent : baseEnd_885688 < baseStart_885688 := by decide
  rcases family_descends (prefixWord ++ tailWord_885688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885716 : List Nat := [2, 4, 1, 2, 1, 3, 3, 2, 1, 2, 2]
def baseStart_885716 : Nat := 118140960795 + 885716 * 2 ^ 59
def prefixEnd_885716 : Nat := 4983230072969 + 3 ^ 40 * 885716 * 2
def baseEnd_885716 : Nat := 454798031377761865776673

theorem tailTrace_885716 : CollatzResearch.WordTrace tailWord_885716 prefixEnd_885716 454798031377761865776673 := by
  unfold tailWord_885716
  simp only [CollatzResearch.WordTrace]
  refine ⟨16152358229604837547414501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21536477639473116729886001 16152358229604837547414501)
  ·
    refine ⟨3028567168050907040140219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16152358229604837547414501 3028567168050907040140219)
    ·
      refine ⟨4542850752076360560210329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3028567168050907040140219 4542850752076360560210329)
      ·
        refine ⟨3407138064057270420157747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4542850752076360560210329 3407138064057270420157747)
        ·
          refine ⟨5110707096085905630236621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3407138064057270420157747 5110707096085905630236621)
          ·
            refine ⟨1916515161032214611338733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5110707096085905630236621 1916515161032214611338733)
            ·
              refine ⟨718693185387080479252025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1916515161032214611338733 718693185387080479252025)
              ·
                refine ⟨539019889040310359439019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 718693185387080479252025 539019889040310359439019)
                ·
                  refine ⟨808529833560465539158529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 539019889040310359439019 808529833560465539158529)
                  ·
                    refine ⟨606397375170349154368897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 808529833560465539158529 606397375170349154368897)
                    ·
                      refine ⟨454798031377761865776673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 606397375170349154368897 454798031377761865776673)
                      ·
                        rfl

theorem cell23_885716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3, 2, 1, 2, 2].length) (baseStart_885716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_885716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_885716 prefixEnd_885716 := by exact prefixLift 885716
  have htrace : WordTrace (prefixWord ++ tailWord_885716) baseStart_885716 baseEnd_885716 := by
    simpa [prefixWord, tailWord_885716, baseEnd_885716] using wordTrace_append hprefix tailTrace_885716
  have hstable : (prefixWord ++ tailWord_885716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885716).length < 2 ^ (prefixWord ++ tailWord_885716).sum := by decide
  have hdescent : baseEnd_885716 < baseStart_885716 := by decide
  rcases family_descends (prefixWord ++ tailWord_885716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885731 : List Nat := [1, 1, 1, 6, 1, 1, 2, 1, 1, 8]
def baseStart_885731 : Nat := 118140960795 + 885731 * 2 ^ 59
def prefixEnd_885731 : Nat := 4983230072969 + 3 ^ 40 * 885731 * 2
def baseEnd_885731 : Nat := 151601911195859769029701

theorem tailTrace_885731 : CollatzResearch.WordTrace tailWord_885731 prefixEnd_885731 151601911195859769029701 := by
  unfold tailWord_885731
  simp only [CollatzResearch.WordTrace]
  refine ⟨32305263554155332656625047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21536842369436888437750031 32305263554155332656625047)
  ·
    refine ⟨48457895331232998984937571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32305263554155332656625047 48457895331232998984937571)
    ·
      refine ⟨72686842996849498477406357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48457895331232998984937571 72686842996849498477406357)
      ·
        refine ⟨3407195765477320241128423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 72686842996849498477406357 3407195765477320241128423)
        ·
          refine ⟨5110793648215980361692635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3407195765477320241128423 5110793648215980361692635)
          ·
            refine ⟨7666190472323970542538953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5110793648215980361692635 7666190472323970542538953)
            ·
              refine ⟨5749642854242977906904215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7666190472323970542538953 5749642854242977906904215)
              ·
                refine ⟨8624464281364466860356323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5749642854242977906904215 8624464281364466860356323)
                ·
                  refine ⟨12936696422046700290534485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8624464281364466860356323 12936696422046700290534485)
                  ·
                    refine ⟨151601911195859769029701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 12936696422046700290534485 151601911195859769029701)
                    ·
                      rfl

theorem cell23_885731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 8].length) (baseStart_885731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_885731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_885731 prefixEnd_885731 := by exact prefixLift 885731
  have htrace : WordTrace (prefixWord ++ tailWord_885731) baseStart_885731 baseEnd_885731 := by
    simpa [prefixWord, tailWord_885731, baseEnd_885731] using wordTrace_append hprefix tailTrace_885731
  have hstable : (prefixWord ++ tailWord_885731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885731).length < 2 ^ (prefixWord ++ tailWord_885731).sum := by decide
  have hdescent : baseEnd_885731 < baseStart_885731 := by decide
  rcases family_descends (prefixWord ++ tailWord_885731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885742 : List Nat := [4, 1, 2, 1, 4, 1, 1, 1, 3, 3, 2]
def baseStart_885742 : Nat := 118140960795 + 885742 * 2 ^ 59
def prefixEnd_885742 : Nat := 4983230072969 + 3 ^ 40 * 885742 * 2
def baseEnd_885742 : Nat := 454811381874778764051553

theorem tailTrace_885742 : CollatzResearch.WordTrace tailWord_885742 prefixEnd_885742 454811381874778764051553 := by
  unfold tailWord_885742
  simp only [CollatzResearch.WordTrace]
  refine ⟨4038208094639435191909435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21537109838076987690183653 4038208094639435191909435)
  ·
    refine ⟨6057312141959152787864153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4038208094639435191909435 6057312141959152787864153)
    ·
      refine ⟨4542984106469364590898115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6057312141959152787864153 4542984106469364590898115)
      ·
        refine ⟨6814476159704046886347173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4542984106469364590898115 6814476159704046886347173)
        ·
          refine ⟨1277714279944508791190095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6814476159704046886347173 1277714279944508791190095)
          ·
            refine ⟨1916571419916763186785143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1277714279944508791190095 1916571419916763186785143)
            ·
              refine ⟨2874857129875144780177715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1916571419916763186785143 2874857129875144780177715)
              ·
                refine ⟨4312285694812717170266573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2874857129875144780177715 4312285694812717170266573)
                ·
                  refine ⟨1617107135554768938849965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4312285694812717170266573 1617107135554768938849965)
                  ·
                    refine ⟨606415175833038352068737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1617107135554768938849965 606415175833038352068737)
                    ·
                      refine ⟨454811381874778764051553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 606415175833038352068737 454811381874778764051553)
                      ·
                        rfl

theorem cell23_885742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 3, 3, 2].length) (baseStart_885742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_885742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_885742 prefixEnd_885742 := by exact prefixLift 885742
  have htrace : WordTrace (prefixWord ++ tailWord_885742) baseStart_885742 baseEnd_885742 := by
    simpa [prefixWord, tailWord_885742, baseEnd_885742] using wordTrace_append hprefix tailTrace_885742
  have hstable : (prefixWord ++ tailWord_885742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885742).length < 2 ^ (prefixWord ++ tailWord_885742).sum := by decide
  have hdescent : baseEnd_885742 < baseStart_885742 := by decide
  rcases family_descends (prefixWord ++ tailWord_885742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885772 : List Nat := [2, 2, 1, 2, 3, 2, 1, 4, 2, 2, 2]
def baseStart_885772 : Nat := 118140960795 + 885772 * 2 ^ 59
def prefixEnd_885772 : Nat := 4983230072969 + 3 ^ 40 * 885772 * 2
def baseEnd_885772 : Nat := 454826786294413646676415

theorem tailTrace_885772 : CollatzResearch.WordTrace tailWord_885772 prefixEnd_885772 454826786294413646676415 := by
  unfold tailWord_885772
  simp only [CollatzResearch.WordTrace]
  refine ⟨16153379473503398329433785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21537839298004531105911713 16153379473503398329433785)
  ·
    refine ⟨12115034605127548747075339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16153379473503398329433785 12115034605127548747075339)
    ·
      refine ⟨18172551907691323120613009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12115034605127548747075339 18172551907691323120613009)
      ·
        refine ⟨13629413930768492340459757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18172551907691323120613009 13629413930768492340459757)
        ·
          refine ⟨5111030224038184627672409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13629413930768492340459757 5111030224038184627672409)
          ·
            refine ⟨3833272668028638470754307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5111030224038184627672409 3833272668028638470754307)
            ·
              refine ⟨5749909002042957706131461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3833272668028638470754307 5749909002042957706131461)
              ·
                refine ⟨1078107937883054569899649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5749909002042957706131461 1078107937883054569899649)
                ·
                  refine ⟨808580953412290927424737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1078107937883054569899649 808580953412290927424737)
                  ·
                    refine ⟨606435715059218195568553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 808580953412290927424737 606435715059218195568553)
                    ·
                      refine ⟨454826786294413646676415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 606435715059218195568553 454826786294413646676415)
                      ·
                        rfl

theorem cell23_885772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 4, 2, 2, 2].length) (baseStart_885772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_885772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_885772 prefixEnd_885772 := by exact prefixLift 885772
  have htrace : WordTrace (prefixWord ++ tailWord_885772) baseStart_885772 baseEnd_885772 := by
    simpa [prefixWord, tailWord_885772, baseEnd_885772] using wordTrace_append hprefix tailTrace_885772
  have hstable : (prefixWord ++ tailWord_885772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885772).length < 2 ^ (prefixWord ++ tailWord_885772).sum := by decide
  have hdescent : baseEnd_885772 < baseStart_885772 := by decide
  rcases family_descends (prefixWord ++ tailWord_885772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885812 : List Nat := [2, 5, 1, 2, 1, 1, 1, 5, 5]
def baseStart_885812 : Nat := 118140960795 + 885812 * 2 ^ 59
def prefixEnd_885812 : Nat := 4983230072969 + 3 ^ 40 * 885812 * 2
def baseEnd_885812 : Nat := 50538591724510387797359

theorem tailTrace_885812 : CollatzResearch.WordTrace tailWord_885812 prefixEnd_885812 50538591724510387797359 := by
  unfold tailWord_885812
  simp only [CollatzResearch.WordTrace]
  refine ⟨16154108933430941745161845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21538811911241255660215793 16154108933430941745161845)
  ·
    refine ⟨1514447712509150788608923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16154108933430941745161845 1514447712509150788608923)
    ·
      refine ⟨2271671568763726182913385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1514447712509150788608923 2271671568763726182913385)
      ·
        refine ⟨1703753676572794637185039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2271671568763726182913385 1703753676572794637185039)
        ·
          refine ⟨2555630514859191955777559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1703753676572794637185039 2555630514859191955777559)
          ·
            refine ⟨3833445772288787933666339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2555630514859191955777559 3833445772288787933666339)
            ·
              refine ⟨5750168658433181900499509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3833445772288787933666339 5750168658433181900499509)
              ·
                refine ⟨539078311728110803171829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5750168658433181900499509 539078311728110803171829)
                ·
                  refine ⟨50538591724510387797359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 539078311728110803171829 50538591724510387797359)
                  ·
                    rfl

theorem cell23_885812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_885812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_885812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_885812 prefixEnd_885812 := by exact prefixLift 885812
  have htrace : WordTrace (prefixWord ++ tailWord_885812) baseStart_885812 baseEnd_885812 := by
    simpa [prefixWord, tailWord_885812, baseEnd_885812] using wordTrace_append hprefix tailTrace_885812
  have hstable : (prefixWord ++ tailWord_885812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885812).length < 2 ^ (prefixWord ++ tailWord_885812).sum := by decide
  have hdescent : baseEnd_885812 < baseStart_885812 := by decide
  rcases family_descends (prefixWord ++ tailWord_885812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885845 : List Nat := [1, 3, 2, 2, 1, 2, 1, 3, 2, 4, 2]
def baseStart_885845 : Nat := 118140960795 + 885845 * 2 ^ 59
def prefixEnd_885845 : Nat := 4983230072969 + 3 ^ 40 * 885845 * 2
def baseEnd_885845 : Nat := 454864270382191861063579

theorem tailTrace_885845 : CollatzResearch.WordTrace tailWord_885845 prefixEnd_885845 454864270382191861063579 := by
  unfold tailWord_885845
  simp only [CollatzResearch.WordTrace]
  refine ⟨32309421475742330126274989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21539614317161553417516659 32309421475742330126274989)
  ·
    refine ⟨12116033053403373797353121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32309421475742330126274989 12116033053403373797353121)
    ·
      refine ⟨9087024790052530348014841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12116033053403373797353121 9087024790052530348014841)
      ·
        refine ⟨6815268592539397761011131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9087024790052530348014841 6815268592539397761011131)
        ·
          refine ⟨10222902888809096641516697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6815268592539397761011131 10222902888809096641516697)
          ·
            refine ⟨7667177166606822481137523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10222902888809096641516697 7667177166606822481137523)
            ·
              refine ⟨11500765749910233721706285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7667177166606822481137523 11500765749910233721706285)
              ·
                refine ⟨4312787156216337645639857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11500765749910233721706285 4312787156216337645639857)
                ·
                  refine ⟨3234590367162253234229893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4312787156216337645639857 3234590367162253234229893)
                  ·
                    refine ⟨606485693842922481418105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3234590367162253234229893 606485693842922481418105)
                    ·
                      refine ⟨454864270382191861063579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 606485693842922481418105 454864270382191861063579)
                      ·
                        rfl

theorem cell23_885845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 2, 4, 2].length) (baseStart_885845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_885845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_885845 prefixEnd_885845 := by exact prefixLift 885845
  have htrace : WordTrace (prefixWord ++ tailWord_885845) baseStart_885845 baseEnd_885845 := by
    simpa [prefixWord, tailWord_885845, baseEnd_885845] using wordTrace_append hprefix tailTrace_885845
  have hstable : (prefixWord ++ tailWord_885845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885845).length < 2 ^ (prefixWord ++ tailWord_885845).sum := by decide
  have hdescent : baseEnd_885845 < baseStart_885845 := by decide
  rcases family_descends (prefixWord ++ tailWord_885845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885848 : List Nat := [2, 1, 2, 2, 1, 3, 1, 1, 3, 4, 3]
def baseStart_885848 : Nat := 118140960795 + 885848 * 2 ^ 59
def prefixEnd_885848 : Nat := 4983230072969 + 3 ^ 40 * 885848 * 2
def baseEnd_885848 : Nat := 454865810824155349326065

theorem tailTrace_885848 : CollatzResearch.WordTrace tailWord_885848 prefixEnd_885848 454865810824155349326065 := by
  unfold tailWord_885848
  simp only [CollatzResearch.WordTrace]
  refine ⟨16154765447365730819317099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21539687263154307759089465 16154765447365730819317099)
  ·
    refine ⟨24232148171048596228975649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16154765447365730819317099 24232148171048596228975649)
    ·
      refine ⟨18174111128286447171731737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24232148171048596228975649 18174111128286447171731737)
      ·
        refine ⟨13630583346214835378798803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18174111128286447171731737 13630583346214835378798803)
        ·
          refine ⟨20445875019322253068198205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13630583346214835378798803 20445875019322253068198205)
          ·
            refine ⟨7667203132245844900574327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20445875019322253068198205 7667203132245844900574327)
            ·
              refine ⟨11500804698368767350861491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7667203132245844900574327 11500804698368767350861491)
              ·
                refine ⟨17251207047553151026292237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11500804698368767350861491 17251207047553151026292237)
                ·
                  refine ⟨6469202642832431634859589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17251207047553151026292237 6469202642832431634859589)
                  ·
                    refine ⟨1212975495531080931536173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6469202642832431634859589 1212975495531080931536173)
                    ·
                      refine ⟨454865810824155349326065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1212975495531080931536173 454865810824155349326065)
                      ·
                        rfl

theorem cell23_885848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 3, 4, 3].length) (baseStart_885848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_885848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_885848 prefixEnd_885848 := by exact prefixLift 885848
  have htrace : WordTrace (prefixWord ++ tailWord_885848) baseStart_885848 baseEnd_885848 := by
    simpa [prefixWord, tailWord_885848, baseEnd_885848] using wordTrace_append hprefix tailTrace_885848
  have hstable : (prefixWord ++ tailWord_885848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885848).length < 2 ^ (prefixWord ++ tailWord_885848).sum := by decide
  have hdescent : baseEnd_885848 < baseStart_885848 := by decide
  rcases family_descends (prefixWord ++ tailWord_885848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885902 : List Nat := [4, 1, 1, 3, 2, 1, 4, 1, 6]
def baseStart_885902 : Nat := 118140960795 + 885902 * 2 ^ 59
def prefixEnd_885902 : Nat := 4983230072969 + 3 ^ 40 * 885902 * 2
def baseEnd_885902 : Nat := 50543726531055348672313

theorem tailTrace_885902 : CollatzResearch.WordTrace tailWord_885902 prefixEnd_885902 50543726531055348672313 := by
  unfold tailWord_885902
  simp only [CollatzResearch.WordTrace]
  refine ⟨4038937554566978607637495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21541000291023885907399973 4038937554566978607637495)
  ·
    refine ⟨6058406331850467911456243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4038937554566978607637495 6058406331850467911456243)
    ·
      refine ⟨9087609497775701867184365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6058406331850467911456243 9087609497775701867184365)
      ·
        refine ⟨3407853561665888200194137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9087609497775701867184365 3407853561665888200194137)
        ·
          refine ⟨2555890171249416150145603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3407853561665888200194137 2555890171249416150145603)
          ·
            refine ⟨3833835256874124225218405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2555890171249416150145603 3833835256874124225218405)
            ·
              refine ⟨718844110663898292228451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3833835256874124225218405 718844110663898292228451)
              ·
                refine ⟨1078266165995847438342677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 718844110663898292228451 1078266165995847438342677)
                ·
                  refine ⟨50543726531055348672313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1078266165995847438342677 50543726531055348672313)
                  ·
                    rfl

theorem cell23_885902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 4, 1, 6].length) (baseStart_885902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_885902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_885902 prefixEnd_885902 := by exact prefixLift 885902
  have htrace : WordTrace (prefixWord ++ tailWord_885902) baseStart_885902 baseEnd_885902 := by
    simpa [prefixWord, tailWord_885902, baseEnd_885902] using wordTrace_append hprefix tailTrace_885902
  have hstable : (prefixWord ++ tailWord_885902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885902).length < 2 ^ (prefixWord ++ tailWord_885902).sum := by decide
  have hdescent : baseEnd_885902 < baseStart_885902 := by decide
  rcases family_descends (prefixWord ++ tailWord_885902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885935 : List Nat := [1, 1, 2, 1, 2, 3, 2, 5, 1, 1, 4]
def baseStart_885935 : Nat := 118140960795 + 885935 * 2 ^ 59
def prefixEnd_885935 : Nat := 4983230072969 + 3 ^ 40 * 885935 * 2
def baseEnd_885935 : Nat := 454910483641096508938165

theorem tailTrace_885935 : CollatzResearch.WordTrace tailWord_885935 prefixEnd_885935 454910483641096508938165 := by
  unfold tailWord_885935
  simp only [CollatzResearch.WordTrace]
  refine ⟨32312704045416275497051259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21541802696944183664700839 32312704045416275497051259)
  ·
    refine ⟨48469056068124413245576889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32312704045416275497051259 48469056068124413245576889)
    ·
      refine ⟨36351792051093309934182667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48469056068124413245576889 36351792051093309934182667)
      ·
        refine ⟨54527688076639964901274001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36351792051093309934182667 54527688076639964901274001)
        ·
          refine ⟨40895766057479973675955501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54527688076639964901274001 40895766057479973675955501)
          ·
            refine ⟨15335912271554990128483313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40895766057479973675955501 15335912271554990128483313)
            ·
              refine ⟨11501934203666242596362485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15335912271554990128483313 11501934203666242596362485)
              ·
                refine ⟨1078306331593710243408983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11501934203666242596362485 1078306331593710243408983)
                ·
                  refine ⟨1617459497390565365113475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1078306331593710243408983 1617459497390565365113475)
                  ·
                    refine ⟨2426189246085848047670213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1617459497390565365113475 2426189246085848047670213)
                    ·
                      refine ⟨454910483641096508938165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2426189246085848047670213 454910483641096508938165)
                      ·
                        rfl

theorem cell23_885935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 5, 1, 1, 4].length) (baseStart_885935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_885935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_885935 prefixEnd_885935 := by exact prefixLift 885935
  have htrace : WordTrace (prefixWord ++ tailWord_885935) baseStart_885935 baseEnd_885935 := by
    simpa [prefixWord, tailWord_885935, baseEnd_885935] using wordTrace_append hprefix tailTrace_885935
  have hstable : (prefixWord ++ tailWord_885935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885935).length < 2 ^ (prefixWord ++ tailWord_885935).sum := by decide
  have hdescent : baseEnd_885935 < baseStart_885935 := by decide
  rcases family_descends (prefixWord ++ tailWord_885935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885962 : List Nat := [3, 1, 2, 1, 3, 2, 2, 3, 2, 4]
def baseStart_885962 : Nat := 118140960795 + 885962 * 2 ^ 59
def prefixEnd_885962 : Nat := 4983230072969 + 3 ^ 40 * 885962 * 2
def baseEnd_885962 : Nat := 151641449206255967766847

theorem tailTrace_885962 : CollatzResearch.WordTrace tailWord_885962 prefixEnd_885962 151641449206255967766847 := by
  unfold tailWord_885962
  simp only [CollatzResearch.WordTrace]
  refine ⟨8078422204079614777071035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21542459210878972738856093 8078422204079614777071035)
  ·
    refine ⟨12117633306119422165606553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8078422204079614777071035 12117633306119422165606553)
    ·
      refine ⟨9088224979589566624204915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12117633306119422165606553 9088224979589566624204915)
      ·
        refine ⟨13632337469384349936307373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9088224979589566624204915 13632337469384349936307373)
        ·
          refine ⟨5112126551019131226115265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13632337469384349936307373 5112126551019131226115265)
          ·
            refine ⟨3834094913264348419586449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5112126551019131226115265 3834094913264348419586449)
            ·
              refine ⟨2875571184948261314689837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3834094913264348419586449 2875571184948261314689837)
              ·
                refine ⟨1078339194355597993008689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2875571184948261314689837 1078339194355597993008689)
                ·
                  refine ⟨808754395766698494756517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1078339194355597993008689 808754395766698494756517)
                  ·
                    refine ⟨151641449206255967766847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 808754395766698494756517 151641449206255967766847)
                    ·
                      rfl

theorem cell23_885962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 3, 2, 4].length) (baseStart_885962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_885962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_885962 prefixEnd_885962 := by exact prefixLift 885962
  have htrace : WordTrace (prefixWord ++ tailWord_885962) baseStart_885962 baseEnd_885962 := by
    simpa [prefixWord, tailWord_885962, baseEnd_885962] using wordTrace_append hprefix tailTrace_885962
  have hstable : (prefixWord ++ tailWord_885962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885962).length < 2 ^ (prefixWord ++ tailWord_885962).sum := by decide
  have hdescent : baseEnd_885962 < baseStart_885962 := by decide
  rcases family_descends (prefixWord ++ tailWord_885962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885989 : List Nat := [1, 3, 1, 4, 3, 1, 1, 3, 1, 2, 3]
def baseStart_885989 : Nat := 118140960795 + 885989 * 2 ^ 59
def prefixEnd_885989 : Nat := 4983230072969 + 3 ^ 40 * 885989 * 2
def baseEnd_885989 : Nat := 454938211596439297662917

theorem tailTrace_885989 : CollatzResearch.WordTrace tailWord_885989 prefixEnd_885989 454938211596439297662917 := by
  unfold tailWord_885989
  simp only [CollatzResearch.WordTrace]
  refine ⟨32314673587220642719517021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21543115724813761813011347 32314673587220642719517021)
  ·
    refine ⟨12118002595207741019818883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32314673587220642719517021 12118002595207741019818883)
    ·
      refine ⟨18177003892811611529728325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12118002595207741019818883 18177003892811611529728325)
      ·
        refine ⟨3408188229902177161824061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18177003892811611529728325 3408188229902177161824061)
        ·
          refine ⟨1278070586213316435684023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3408188229902177161824061 1278070586213316435684023)
          ·
            refine ⟨1917105879319974653526035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1278070586213316435684023 1917105879319974653526035)
            ·
              refine ⟨2875658818979961980289053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1917105879319974653526035 2875658818979961980289053)
              ·
                refine ⟨1078372057117485742608395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2875658818979961980289053 1078372057117485742608395)
                ·
                  refine ⟨1617558085676228613912593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1078372057117485742608395 1617558085676228613912593)
                  ·
                    refine ⟨1213168564257171460434445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1617558085676228613912593 1213168564257171460434445)
                    ·
                      refine ⟨454938211596439297662917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1213168564257171460434445 454938211596439297662917)
                      ·
                        rfl

theorem cell23_885989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_885989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_885989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_885989 prefixEnd_885989 := by exact prefixLift 885989
  have htrace : WordTrace (prefixWord ++ tailWord_885989) baseStart_885989 baseEnd_885989 := by
    simpa [prefixWord, tailWord_885989, baseEnd_885989] using wordTrace_append hprefix tailTrace_885989
  have hstable : (prefixWord ++ tailWord_885989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885989).length < 2 ^ (prefixWord ++ tailWord_885989).sum := by decide
  have hdescent : baseEnd_885989 < baseStart_885989 := by decide
  rcases family_descends (prefixWord ++ tailWord_885989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886075 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 8, 3, 3]
def baseStart_886075 : Nat := 118140960795 + 886075 * 2 ^ 59
def prefixEnd_886075 : Nat := 4983230072969 + 3 ^ 40 * 886075 * 2
def baseEnd_886075 : Nat := 454982370932725961187521

theorem tailTrace_886075 : CollatzResearch.WordTrace tailWord_886075 prefixEnd_886075 454982370932725961187521 := by
  unfold tailWord_886075
  simp only [CollatzResearch.WordTrace]
  refine ⟨32317810264909079407147679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21545206843272719604765119 32317810264909079407147679)
  ·
    refine ⟨48476715397363619110721519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32317810264909079407147679 48476715397363619110721519)
    ·
      refine ⟨72715073096045428666082279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48476715397363619110721519 72715073096045428666082279)
      ·
        refine ⟨109072609644068142999123419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72715073096045428666082279 109072609644068142999123419)
        ·
          refine ⟨163608914466102214498685129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109072609644068142999123419 163608914466102214498685129)
          ·
            refine ⟨122706685849576660874013847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163608914466102214498685129 122706685849576660874013847)
            ·
              refine ⟨184060028774364991311020771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122706685849576660874013847 184060028774364991311020771)
              ·
                refine ⟨276090043161547486966531157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184060028774364991311020771 276090043161547486966531157)
                ·
                  refine ⟨3235430193299384612889037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 276090043161547486966531157 3235430193299384612889037)
                  ·
                    refine ⟨1213286322487269229833389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3235430193299384612889037 1213286322487269229833389)
                    ·
                      refine ⟨454982370932725961187521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1213286322487269229833389 454982370932725961187521)
                      ·
                        rfl

theorem cell23_886075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 8, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 8, 3, 3].length) (baseStart_886075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_886075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_886075 prefixEnd_886075 := by exact prefixLift 886075
  have htrace : WordTrace (prefixWord ++ tailWord_886075) baseStart_886075 baseEnd_886075 := by
    simpa [prefixWord, tailWord_886075, baseEnd_886075] using wordTrace_append hprefix tailTrace_886075
  have hstable : (prefixWord ++ tailWord_886075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886075).length < 2 ^ (prefixWord ++ tailWord_886075).sum := by decide
  have hdescent : baseEnd_886075 < baseStart_886075 := by decide
  rcases family_descends (prefixWord ++ tailWord_886075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886076 : List Nat := [2, 2, 2, 2, 1, 4, 1, 3, 2, 2, 2]
def baseStart_886076 : Nat := 118140960795 + 886076 * 2 ^ 59
def prefixEnd_886076 : Nat := 4983230072969 + 3 ^ 40 * 886076 * 2
def baseEnd_886076 : Nat := 454982884413380457275017

theorem tailTrace_886076 : CollatzResearch.WordTrace tailWord_886076 prefixEnd_886076 454982884413380457275017 := by
  unfold tailWord_886076
  simp only [CollatzResearch.WordTrace]
  refine ⟨16158923368952728288967041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21545231158603637718622721 16158923368952728288967041)
  ·
    refine ⟨12119192526714546216725281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16158923368952728288967041 12119192526714546216725281)
    ·
      refine ⟨9089394395035909662543961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12119192526714546216725281 9089394395035909662543961)
      ·
        refine ⟨6817045796276932246907971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9089394395035909662543961 6817045796276932246907971)
        ·
          refine ⟨10225568694415398370361957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6817045796276932246907971 10225568694415398370361957)
          ·
            refine ⟨1917294130202887194442867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10225568694415398370361957 1917294130202887194442867)
            ·
              refine ⟨2875941195304330791664301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1917294130202887194442867 2875941195304330791664301)
              ·
                refine ⟨1078477948239124046874113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2875941195304330791664301 1078477948239124046874113)
                ·
                  refine ⟨808858461179343035155585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1078477948239124046874113 808858461179343035155585)
                  ·
                    refine ⟨606643845884507276366689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 808858461179343035155585 606643845884507276366689)
                    ·
                      refine ⟨454982884413380457275017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 606643845884507276366689 454982884413380457275017)
                      ·
                        rfl

theorem cell23_886076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 3, 2, 2, 2].length) (baseStart_886076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_886076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_886076 prefixEnd_886076 := by exact prefixLift 886076
  have htrace : WordTrace (prefixWord ++ tailWord_886076) baseStart_886076 baseEnd_886076 := by
    simpa [prefixWord, tailWord_886076, baseEnd_886076] using wordTrace_append hprefix tailTrace_886076
  have hstable : (prefixWord ++ tailWord_886076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886076).length < 2 ^ (prefixWord ++ tailWord_886076).sum := by decide
  have hdescent : baseEnd_886076 < baseStart_886076 := by decide
  rcases family_descends (prefixWord ++ tailWord_886076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886093 : List Nat := [1, 6, 1, 3, 1, 1, 1, 2, 1, 4, 2]
def baseStart_886093 : Nat := 118140960795 + 886093 * 2 ^ 59
def prefixEnd_886093 : Nat := 4983230072969 + 3 ^ 40 * 886093 * 2
def baseEnd_886093 : Nat := 454991613584506890762439

theorem tailTrace_886093 : CollatzResearch.WordTrace tailWord_886093 prefixEnd_886093 454991613584506890762439 := by
  unfold tailWord_886093
  simp only [CollatzResearch.WordTrace]
  refine ⟨32318466778843868481302933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21545644519229245654201955 32318466778843868481302933)
  ·
    refine ⟨1514928130258306335061075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 32318466778843868481302933 1514928130258306335061075)
    ·
      refine ⟨2272392195387459502591613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1514928130258306335061075 2272392195387459502591613)
      ·
        refine ⟨852147073270297313471855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2272392195387459502591613 852147073270297313471855)
        ·
          refine ⟨1278220609905445970207783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 852147073270297313471855 1278220609905445970207783)
          ·
            refine ⟨1917330914858168955311675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1278220609905445970207783 1917330914858168955311675)
            ·
              refine ⟨2875996372287253432967513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1917330914858168955311675 2875996372287253432967513)
              ·
                refine ⟨2156997279215440074725635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2875996372287253432967513 2156997279215440074725635)
                ·
                  refine ⟨3235495918823160112088453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2156997279215440074725635 3235495918823160112088453)
                  ·
                    refine ⟨606655484779342521016585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3235495918823160112088453 606655484779342521016585)
                    ·
                      refine ⟨454991613584506890762439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 606655484779342521016585 454991613584506890762439)
                      ·
                        rfl

theorem cell23_886093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_886093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_886093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_886093 prefixEnd_886093 := by exact prefixLift 886093
  have htrace : WordTrace (prefixWord ++ tailWord_886093) baseStart_886093 baseEnd_886093 := by
    simpa [prefixWord, tailWord_886093, baseEnd_886093] using wordTrace_append hprefix tailTrace_886093
  have hstable : (prefixWord ++ tailWord_886093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886093).length < 2 ^ (prefixWord ++ tailWord_886093).sum := by decide
  have hdescent : baseEnd_886093 < baseStart_886093 := by decide
  rcases family_descends (prefixWord ++ tailWord_886093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886105 : List Nat := [1, 2, 1, 2, 2, 2, 3, 2, 1, 2, 5]
def baseStart_886105 : Nat := 118140960795 + 886105 * 2 ^ 59
def prefixEnd_886105 : Nat := 4983230072969 + 3 ^ 40 * 886105 * 2
def baseEnd_886105 : Nat := 454997775352360843812383

theorem tailTrace_886105 : CollatzResearch.WordTrace tailWord_886105 prefixEnd_886105 454997775352360843812383 := by
  unfold tailWord_886105
  simp only [CollatzResearch.WordTrace]
  refine ⟨32318904454800394530739769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21545936303200263020493179 32318904454800394530739769)
  ·
    refine ⟨24239178341100295898054827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32318904454800394530739769 24239178341100295898054827)
    ·
      refine ⟨36358767511650443847082241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24239178341100295898054827 36358767511650443847082241)
      ·
        refine ⟨27269075633737832885311681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36358767511650443847082241 27269075633737832885311681)
        ·
          refine ⟨20451806725303374663983761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27269075633737832885311681 20451806725303374663983761)
          ·
            refine ⟨15338855043977530997987821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20451806725303374663983761 15338855043977530997987821)
            ·
              refine ⟨5752070641491574124245433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15338855043977530997987821 5752070641491574124245433)
              ·
                refine ⟨4314052981118680593184075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5752070641491574124245433 4314052981118680593184075)
                ·
                  refine ⟨6471079471678020889776113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4314052981118680593184075 6471079471678020889776113)
                  ·
                    refine ⟨4853309603758515667332085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6471079471678020889776113 4853309603758515667332085)
                    ·
                      refine ⟨454997775352360843812383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4853309603758515667332085 454997775352360843812383)
                      ·
                        rfl

theorem cell23_886105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 2, 5].length) (baseStart_886105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_886105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_886105 prefixEnd_886105 := by exact prefixLift 886105
  have htrace : WordTrace (prefixWord ++ tailWord_886105) baseStart_886105 baseEnd_886105 := by
    simpa [prefixWord, tailWord_886105, baseEnd_886105] using wordTrace_append hprefix tailTrace_886105
  have hstable : (prefixWord ++ tailWord_886105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886105).length < 2 ^ (prefixWord ++ tailWord_886105).sum := by decide
  have hdescent : baseEnd_886105 < baseStart_886105 := by decide
  rcases family_descends (prefixWord ++ tailWord_886105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886112 : List Nat := [2, 1, 1, 3, 4, 1, 2, 2, 2, 5]
def baseStart_886112 : Nat := 118140960795 + 886112 * 2 ^ 59
def prefixEnd_886112 : Nat := 4983230072969 + 3 ^ 40 * 886112 * 2
def baseEnd_886112 : Nat := 151667123238980772141617

theorem tailTrace_886112 : CollatzResearch.WordTrace tailWord_886112 prefixEnd_886112 151667123238980772141617 := by
  unfold tailWord_886112
  simp only [CollatzResearch.WordTrace]
  refine ⟨16159579882887517363122295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21546106510516689817496393 16159579882887517363122295)
  ·
    refine ⟨24239369824331276044683443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16159579882887517363122295 24239369824331276044683443)
    ·
      refine ⟨36359054736496914067025165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24239369824331276044683443 36359054736496914067025165)
      ·
        refine ⟨13634645526186342775134437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36359054736496914067025165 13634645526186342775134437)
        ·
          refine ⟨2556496036159939270337707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13634645526186342775134437 2556496036159939270337707)
          ·
            refine ⟨3834744054239908905506561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2556496036159939270337707 3834744054239908905506561)
            ·
              refine ⟨2876058040679931679129921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3834744054239908905506561 2876058040679931679129921)
              ·
                refine ⟨2157043530509948759347441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2876058040679931679129921 2157043530509948759347441)
                ·
                  refine ⟨1617782647882461569510581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2157043530509948759347441 1617782647882461569510581)
                  ·
                    refine ⟨151667123238980772141617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1617782647882461569510581 151667123238980772141617)
                    ·
                      rfl

theorem cell23_886112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 2, 2, 5].length) (baseStart_886112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_886112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_886112 prefixEnd_886112 := by exact prefixLift 886112
  have htrace : WordTrace (prefixWord ++ tailWord_886112) baseStart_886112 baseEnd_886112 := by
    simpa [prefixWord, tailWord_886112, baseEnd_886112] using wordTrace_append hprefix tailTrace_886112
  have hstable : (prefixWord ++ tailWord_886112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886112).length < 2 ^ (prefixWord ++ tailWord_886112).sum := by decide
  have hdescent : baseEnd_886112 < baseStart_886112 := by decide
  rcases family_descends (prefixWord ++ tailWord_886112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886116 : List Nat := [2, 3, 1, 1, 3, 4, 2, 2, 5]
def baseStart_886116 : Nat := 118140960795 + 886116 * 2 ^ 59
def prefixEnd_886116 : Nat := 4983230072969 + 3 ^ 40 * 886116 * 2
def baseEnd_886116 : Nat := 50555935959951144530537

theorem tailTrace_886116 : CollatzResearch.WordTrace tailWord_886116 prefixEnd_886116 50555935959951144530537 := by
  unfold tailWord_886116
  simp only [CollatzResearch.WordTrace]
  refine ⟨16159652828880271704695101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21546203771840362272926801 16159652828880271704695101)
  ·
    refine ⟨6059869810830101889260663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16159652828880271704695101 6059869810830101889260663)
    ·
      refine ⟨9089804716245152833890995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6059869810830101889260663 9089804716245152833890995)
      ·
        refine ⟨13634707074367729250836493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9089804716245152833890995 13634707074367729250836493)
        ·
          refine ⟨5113015152887898469063685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13634707074367729250836493 5113015152887898469063685)
          ·
            refine ⟨958690341166480962949441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5113015152887898469063685 958690341166480962949441)
            ·
              refine ⟨719017755874860722212081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 958690341166480962949441 719017755874860722212081)
              ·
                refine ⟨539263316906145541659061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 719017755874860722212081 539263316906145541659061)
                ·
                  refine ⟨50555935959951144530537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 539263316906145541659061 50555935959951144530537)
                  ·
                    rfl

theorem cell23_886116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 2, 2, 5].length) (baseStart_886116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_886116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_886116 prefixEnd_886116 := by exact prefixLift 886116
  have htrace : WordTrace (prefixWord ++ tailWord_886116) baseStart_886116 baseEnd_886116 := by
    simpa [prefixWord, tailWord_886116, baseEnd_886116] using wordTrace_append hprefix tailTrace_886116
  have hstable : (prefixWord ++ tailWord_886116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886116).length < 2 ^ (prefixWord ++ tailWord_886116).sum := by decide
  have hdescent : baseEnd_886116 < baseStart_886116 := by decide
  rcases family_descends (prefixWord ++ tailWord_886116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886126 : List Nat := [4, 1, 2, 4, 1, 1, 1, 1, 2, 3, 3]
def baseStart_886126 : Nat := 118140960795 + 886126 * 2 ^ 59
def prefixEnd_886126 : Nat := 4983230072969 + 3 ^ 40 * 886126 * 2
def baseEnd_886126 : Nat := 455008558446105261649787

theorem tailTrace_886126 : CollatzResearch.WordTrace tailWord_886126 prefixEnd_886126 455008558446105261649787 := by
  unfold tailWord_886126
  simp only [CollatzResearch.WordTrace]
  refine ⟨4039958798465539389656779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21546446925149543411502821 4039958798465539389656779)
  ·
    refine ⟨6059938197698309084485169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4039958798465539389656779 6059938197698309084485169)
    ·
      refine ⟨4544953648273731813363877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6059938197698309084485169 4544953648273731813363877)
      ·
        refine ⟨852178809051324715005727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4544953648273731813363877 852178809051324715005727)
        ·
          refine ⟨1278268213576987072508591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 852178809051324715005727 1278268213576987072508591)
          ·
            refine ⟨1917402320365480608762887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1278268213576987072508591 1917402320365480608762887)
            ·
              refine ⟨2876103480548220913144331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1917402320365480608762887 2876103480548220913144331)
              ·
                refine ⟨4314155220822331369716497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2876103480548220913144331 4314155220822331369716497)
                ·
                  refine ⟨3235616415616748527287373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4314155220822331369716497 3235616415616748527287373)
                  ·
                    refine ⟨1213356155856280697732765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3235616415616748527287373 1213356155856280697732765)
                    ·
                      refine ⟨455008558446105261649787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1213356155856280697732765 455008558446105261649787)
                      ·
                        rfl

theorem cell23_886126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_886126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_886126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_886126 prefixEnd_886126 := by exact prefixLift 886126
  have htrace : WordTrace (prefixWord ++ tailWord_886126) baseStart_886126 baseEnd_886126 := by
    simpa [prefixWord, tailWord_886126, baseEnd_886126] using wordTrace_append hprefix tailTrace_886126
  have hstable : (prefixWord ++ tailWord_886126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886126).length < 2 ^ (prefixWord ++ tailWord_886126).sum := by decide
  have hdescent : baseEnd_886126 < baseStart_886126 := by decide
  rcases family_descends (prefixWord ++ tailWord_886126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886146 : List Nat := [3, 4, 2, 1, 1, 1, 3, 1, 2, 5]
def baseStart_886146 : Nat := 118140960795 + 886146 * 2 ^ 59
def prefixEnd_886146 : Nat := 4983230072969 + 3 ^ 40 * 886146 * 2
def baseEnd_886146 : Nat := 151672942686398394466565

theorem tailTrace_886146 : CollatzResearch.WordTrace tailWord_886146 prefixEnd_886146 151672942686398394466565 := by
  unfold tailWord_886146
  simp only [CollatzResearch.WordTrace]
  refine ⟨8080099961912964633245573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21546933231767905688654861 8080099961912964633245573)
  ·
    refine ⟨1515018742858680868733545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8080099961912964633245573 1515018742858680868733545)
    ·
      refine ⟨1136264057144010651550159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1515018742858680868733545 1136264057144010651550159)
      ·
        refine ⟨1704396085716015977325239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1136264057144010651550159 1704396085716015977325239)
        ·
          refine ⟨2556594128574023965987859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1704396085716015977325239 2556594128574023965987859)
          ·
            refine ⟨3834891192861035948981789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2556594128574023965987859 3834891192861035948981789)
            ·
              refine ⟨1438084197322888480868171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3834891192861035948981789 1438084197322888480868171)
              ·
                refine ⟨2157126295984332721302257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1438084197322888480868171 2157126295984332721302257)
                ·
                  refine ⟨1617844721988249540976693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2157126295984332721302257 1617844721988249540976693)
                  ·
                    refine ⟨151672942686398394466565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1617844721988249540976693 151672942686398394466565)
                    ·
                      rfl

theorem cell23_886146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_886146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_886146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_886146 prefixEnd_886146 := by exact prefixLift 886146
  have htrace : WordTrace (prefixWord ++ tailWord_886146) baseStart_886146 baseEnd_886146 := by
    simpa [prefixWord, tailWord_886146, baseEnd_886146] using wordTrace_append hprefix tailTrace_886146
  have hstable : (prefixWord ++ tailWord_886146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886146).length < 2 ^ (prefixWord ++ tailWord_886146).sum := by decide
  have hdescent : baseEnd_886146 < baseStart_886146 := by decide
  rcases family_descends (prefixWord ++ tailWord_886146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886155 : List Nat := [1, 1, 1, 1, 4, 3, 2, 2, 8]
def baseStart_886155 : Nat := 118140960795 + 886155 * 2 ^ 59
def prefixEnd_886155 : Nat := 4983230072969 + 3 ^ 40 * 886155 * 2
def baseEnd_886155 : Nat := 50558161042787294243017

theorem tailTrace_886155 : CollatzResearch.WordTrace tailWord_886155 prefixEnd_886155 50558161042787294243017 := by
  unfold tailWord_886155
  simp only [CollatzResearch.WordTrace]
  refine ⟨32320728104619253070059919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21547152069746168713373279 32320728104619253070059919)
  ·
    refine ⟨48481092156928879605089879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32320728104619253070059919 48481092156928879605089879)
    ·
      refine ⟨72721638235393319407634819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48481092156928879605089879 72721638235393319407634819)
      ·
        refine ⟨109082457353089979111452229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72721638235393319407634819 109082457353089979111452229)
        ·
          refine ⟨20452960753704371083397293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109082457353089979111452229 20452960753704371083397293)
          ·
            refine ⟨7669860282639139156273985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20452960753704371083397293 7669860282639139156273985)
            ·
              refine ⟨5752395211979354367205489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7669860282639139156273985 5752395211979354367205489)
              ·
                refine ⟨4314296408984515775404117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5752395211979354367205489 4314296408984515775404117)
                ·
                  refine ⟨50558161042787294243017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4314296408984515775404117 50558161042787294243017)
                  ·
                    rfl

theorem cell23_886155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 8].length) (baseStart_886155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_886155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_886155 prefixEnd_886155 := by exact prefixLift 886155
  have htrace : WordTrace (prefixWord ++ tailWord_886155) baseStart_886155 baseEnd_886155 := by
    simpa [prefixWord, tailWord_886155, baseEnd_886155] using wordTrace_append hprefix tailTrace_886155
  have hstable : (prefixWord ++ tailWord_886155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886155).length < 2 ^ (prefixWord ++ tailWord_886155).sum := by decide
  have hdescent : baseEnd_886155 < baseStart_886155 := by decide
  rcases family_descends (prefixWord ++ tailWord_886155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886195 : List Nat := [1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 7]
def baseStart_886195 : Nat := 118140960795 + 886195 * 2 ^ 59
def prefixEnd_886195 : Nat := 4983230072969 + 3 ^ 40 * 886195 * 2
def baseEnd_886195 : Nat := 455043988611265491686969

theorem tailTrace_886195 : CollatzResearch.WordTrace tailWord_886195 prefixEnd_886195 455043988611265491686969 := by
  unfold tailWord_886195
  simp only [CollatzResearch.WordTrace]
  refine ⟨32322187024474339901516039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21548124682982893267677359 32322187024474339901516039)
  ·
    refine ⟨48483280536711509852274059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32322187024474339901516039 48483280536711509852274059)
    ·
      refine ⟨72724920805067264778411089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48483280536711509852274059 72724920805067264778411089)
      ·
        refine ⟨54543690603800448583808317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72724920805067264778411089 54543690603800448583808317)
        ·
          refine ⟨20453883976425168218928119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54543690603800448583808317 20453883976425168218928119)
          ·
            refine ⟨30680825964637752328392179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20453883976425168218928119 30680825964637752328392179)
            ·
              refine ⟨46021238946956628492588269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30680825964637752328392179 46021238946956628492588269)
              ·
                refine ⟨17257964605108735684720601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46021238946956628492588269 17257964605108735684720601)
                ·
                  refine ⟨12943473453831551763540451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17257964605108735684720601 12943473453831551763540451)
                  ·
                    refine ⟨19415210180747327645310677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12943473453831551763540451 19415210180747327645310677)
                    ·
                      refine ⟨455043988611265491686969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 19415210180747327645310677 455043988611265491686969)
                      ·
                        rfl

theorem cell23_886195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 7].length) (baseStart_886195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_886195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_886195 prefixEnd_886195 := by exact prefixLift 886195
  have htrace : WordTrace (prefixWord ++ tailWord_886195) baseStart_886195 baseEnd_886195 := by
    simpa [prefixWord, tailWord_886195, baseEnd_886195] using wordTrace_append hprefix tailTrace_886195
  have hstable : (prefixWord ++ tailWord_886195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886195).length < 2 ^ (prefixWord ++ tailWord_886195).sum := by decide
  have hdescent : baseEnd_886195 < baseStart_886195 := by decide
  rcases family_descends (prefixWord ++ tailWord_886195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886199 : List Nat := [1, 1, 3, 1, 3, 2, 1, 4, 3, 1, 3]
def baseStart_886199 : Nat := 118140960795 + 886199 * 2 ^ 59
def prefixEnd_886199 : Nat := 4983230072969 + 3 ^ 40 * 886199 * 2
def baseEnd_886199 : Nat := 455046042533883476036951

theorem tailTrace_886199 : CollatzResearch.WordTrace tailWord_886199 prefixEnd_886199 455046042533883476036951 := by
  unfold tailWord_886199
  simp only [CollatzResearch.WordTrace]
  refine ⟨32322332916459848584661651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21548221944306565723107767 32322332916459848584661651)
  ·
    refine ⟨48483499374689772876992477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32322332916459848584661651 48483499374689772876992477)
    ·
      refine ⟨18181312265508664828872179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48483499374689772876992477 18181312265508664828872179)
      ·
        refine ⟨27271968398262997243308269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18181312265508664828872179 27271968398262997243308269)
        ·
          refine ⟨10226988149348623966240601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27271968398262997243308269 10226988149348623966240601)
          ·
            refine ⟨7670241112011467974680451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10226988149348623966240601 7670241112011467974680451)
            ·
              refine ⟨11505361668017201962020677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7670241112011467974680451 11505361668017201962020677)
              ·
                refine ⟨2157255312753225367878877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11505361668017201962020677 2157255312753225367878877)
                ·
                  refine ⟨808970742282459512954579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2157255312753225367878877 808970742282459512954579)
                  ·
                    refine ⟨1213456113423689269431869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 808970742282459512954579 1213456113423689269431869)
                    ·
                      refine ⟨455046042533883476036951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1213456113423689269431869 455046042533883476036951)
                      ·
                        rfl

theorem cell23_886199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 4, 3, 1, 3].length) (baseStart_886199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_886199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_886199 prefixEnd_886199 := by exact prefixLift 886199
  have htrace : WordTrace (prefixWord ++ tailWord_886199) baseStart_886199 baseEnd_886199 := by
    simpa [prefixWord, tailWord_886199, baseEnd_886199] using wordTrace_append hprefix tailTrace_886199
  have hstable : (prefixWord ++ tailWord_886199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886199).length < 2 ^ (prefixWord ++ tailWord_886199).sum := by decide
  have hdescent : baseEnd_886199 < baseStart_886199 := by decide
  rcases family_descends (prefixWord ++ tailWord_886199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886253 : List Nat := [1, 5, 1, 3, 2, 2, 1, 2, 1, 5]
def baseStart_886253 : Nat := 118140960795 + 886253 * 2 ^ 59
def prefixEnd_886253 : Nat := 4983230072969 + 3 ^ 40 * 886253 * 2
def baseEnd_886253 : Nat := 151691256829742088253901

theorem tailTrace_886253 : CollatzResearch.WordTrace tailWord_886253 prefixEnd_886253 151691256829742088253901 := by
  unfold tailWord_886253
  simp only [CollatzResearch.WordTrace]
  refine ⟨32324302458264215807127413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21549534972176143871418275 32324302458264215807127413)
  ·
    refine ⟨3030403355462270231918195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32324302458264215807127413 3030403355462270231918195)
    ·
      refine ⟨4545605033193405347877293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3030403355462270231918195 4545605033193405347877293)
      ·
        refine ⟨1704601887447527005453985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4545605033193405347877293 1704601887447527005453985)
        ·
          refine ⟨1278451415585645254090489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1704601887447527005453985 1278451415585645254090489)
          ·
            refine ⟨958838561689233940567867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1278451415585645254090489 958838561689233940567867)
            ·
              refine ⟨1438257842533850910851801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 958838561689233940567867 1438257842533850910851801)
              ·
                refine ⟨1078693381900388183138851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1438257842533850910851801 1078693381900388183138851)
                ·
                  refine ⟨1618040072850582274708277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1078693381900388183138851 1618040072850582274708277)
                  ·
                    refine ⟨151691256829742088253901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1618040072850582274708277 151691256829742088253901)
                    ·
                      rfl

theorem cell23_886253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_886253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_886253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_886253 prefixEnd_886253 := by exact prefixLift 886253
  have htrace : WordTrace (prefixWord ++ tailWord_886253) baseStart_886253 baseEnd_886253 := by
    simpa [prefixWord, tailWord_886253, baseEnd_886253] using wordTrace_append hprefix tailTrace_886253
  have hstable : (prefixWord ++ tailWord_886253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886253).length < 2 ^ (prefixWord ++ tailWord_886253).sum := by decide
  have hdescent : baseEnd_886253 < baseStart_886253 := by decide
  rcases family_descends (prefixWord ++ tailWord_886253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886256 : List Nat := [2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 4]
def baseStart_886256 : Nat := 118140960795 + 886256 * 2 ^ 59
def prefixEnd_886256 : Nat := 4983230072969 + 3 ^ 40 * 886256 * 2
def baseEnd_886256 : Nat := 455075310931189753024189

theorem tailTrace_886256 : CollatzResearch.WordTrace tailWord_886256 prefixEnd_886256 455075310931189753024189 := by
  unfold tailWord_886256
  simp only [CollatzResearch.WordTrace]
  refine ⟨16162205938626673659743311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21549607918168898212991081 16162205938626673659743311)
  ·
    refine ⟨24243308907940010489614967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16162205938626673659743311 24243308907940010489614967)
    ·
      refine ⟨36364963361910015734422451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24243308907940010489614967 36364963361910015734422451)
      ·
        refine ⟨54547445042865023601633677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36364963361910015734422451 54547445042865023601633677)
        ·
          refine ⟨20455291891074383850612629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54547445042865023601633677 20455291891074383850612629)
          ·
            refine ⟨958841807394111742997467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 20455291891074383850612629 958841807394111742997467)
            ·
              refine ⟨1438262711091167614496201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 958841807394111742997467 1438262711091167614496201)
              ·
                refine ⟨1078697033318375710872151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1438262711091167614496201 1078697033318375710872151)
                ·
                  refine ⟨1618045549977563566308227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1078697033318375710872151 1618045549977563566308227)
                  ·
                    refine ⟨2427068324966345349462341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1618045549977563566308227 2427068324966345349462341)
                    ·
                      refine ⟨455075310931189753024189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2427068324966345349462341 455075310931189753024189)
                      ·
                        rfl

theorem cell23_886256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 4].length) (baseStart_886256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_886256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_886256 prefixEnd_886256 := by exact prefixLift 886256
  have htrace : WordTrace (prefixWord ++ tailWord_886256) baseStart_886256 baseEnd_886256 := by
    simpa [prefixWord, tailWord_886256, baseEnd_886256] using wordTrace_append hprefix tailTrace_886256
  have hstable : (prefixWord ++ tailWord_886256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886256).length < 2 ^ (prefixWord ++ tailWord_886256).sum := by decide
  have hdescent : baseEnd_886256 < baseStart_886256 := by decide
  rcases family_descends (prefixWord ++ tailWord_886256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886259 : List Nat := [1, 1, 1, 2, 2, 2, 2, 6, 1, 2, 3]
def baseStart_886259 : Nat := 118140960795 + 886259 * 2 ^ 59
def prefixEnd_886259 : Nat := 4983230072969 + 3 ^ 40 * 886259 * 2
def baseEnd_886259 : Nat := 455076851373153241286675

theorem tailTrace_886259 : CollatzResearch.WordTrace tailWord_886259 prefixEnd_886259 455076851373153241286675 := by
  unfold tailWord_886259
  simp only [CollatzResearch.WordTrace]
  refine ⟨32324521296242478831845831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21549680864161652554563887 32324521296242478831845831)
  ·
    refine ⟨48486781944363718247768747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32324521296242478831845831 48486781944363718247768747)
    ·
      refine ⟨72730172916545577371653121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48486781944363718247768747 72730172916545577371653121)
      ·
        refine ⟨54547629687409183028739841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72730172916545577371653121 54547629687409183028739841)
        ·
          refine ⟨40910722265556887271554881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54547629687409183028739841 40910722265556887271554881)
          ·
            refine ⟨30683041699167665453666161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40910722265556887271554881 30683041699167665453666161)
            ·
              refine ⟨23012281274375749090249621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30683041699167665453666161 23012281274375749090249621)
              ·
                refine ⟨1078700684736363238605451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23012281274375749090249621 1078700684736363238605451)
                ·
                  refine ⟨1618051027104544857908177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1078700684736363238605451 1618051027104544857908177)
                  ·
                    refine ⟨1213538270328408643431133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1618051027104544857908177 1213538270328408643431133)
                    ·
                      refine ⟨455076851373153241286675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1213538270328408643431133 455076851373153241286675)
                      ·
                        rfl

theorem cell23_886259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 6, 1, 2, 3].length) (baseStart_886259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_886259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_886259 prefixEnd_886259 := by exact prefixLift 886259
  have htrace : WordTrace (prefixWord ++ tailWord_886259) baseStart_886259 baseEnd_886259 := by
    simpa [prefixWord, tailWord_886259, baseEnd_886259] using wordTrace_append hprefix tailTrace_886259
  have hstable : (prefixWord ++ tailWord_886259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886259).length < 2 ^ (prefixWord ++ tailWord_886259).sum := by decide
  have hdescent : baseEnd_886259 < baseStart_886259 := by decide
  rcases family_descends (prefixWord ++ tailWord_886259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886269 : List Nat := [1, 4, 1, 1, 1, 5, 1, 2, 1, 2, 4]
def baseStart_886269 : Nat := 118140960795 + 886269 * 2 ^ 59
def prefixEnd_886269 : Nat := 4983230072969 + 3 ^ 40 * 886269 * 2
def baseEnd_886269 : Nat := 455081986179698202161629

theorem tailTrace_886269 : CollatzResearch.WordTrace tailWord_886269 prefixEnd_886269 455081986179698202161629 := by
  unfold tailWord_886269
  simp only [CollatzResearch.WordTrace]
  refine ⟨32324886026206250539709861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21549924017470833693139907 32324886026206250539709861)
  ·
    refine ⟨6060916129913671976195599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32324886026206250539709861 6060916129913671976195599)
    ·
      refine ⟨9091374194870507964293399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6060916129913671976195599 9091374194870507964293399)
      ·
        refine ⟨13637061292305761946440099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9091374194870507964293399 13637061292305761946440099)
        ·
          refine ⟨20455591938458642919660149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13637061292305761946440099 20455591938458642919660149)
          ·
            refine ⟨1917711744230497773718139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20455591938458642919660149 1917711744230497773718139)
            ·
              refine ⟨2876567616345746660577209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1917711744230497773718139 2876567616345746660577209)
              ·
                refine ⟨2157425712259309995432907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2876567616345746660577209 2157425712259309995432907)
                ·
                  refine ⟨3236138568388964993149361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2157425712259309995432907 3236138568388964993149361)
                  ·
                    refine ⟨2427103926291723744862021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3236138568388964993149361 2427103926291723744862021)
                    ·
                      refine ⟨455081986179698202161629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2427103926291723744862021 455081986179698202161629)
                      ·
                        rfl

theorem cell23_886269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 2, 1, 2, 4].length) (baseStart_886269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_886269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_886269 prefixEnd_886269 := by exact prefixLift 886269
  have htrace : WordTrace (prefixWord ++ tailWord_886269) baseStart_886269 baseEnd_886269 := by
    simpa [prefixWord, tailWord_886269, baseEnd_886269] using wordTrace_append hprefix tailTrace_886269
  have hstable : (prefixWord ++ tailWord_886269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886269).length < 2 ^ (prefixWord ++ tailWord_886269).sum := by decide
  have hdescent : baseEnd_886269 < baseStart_886269 := by decide
  rcases family_descends (prefixWord ++ tailWord_886269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886270 : List Nat := [4, 2, 2, 3, 1, 1, 3, 1, 1, 5]
def baseStart_886270 : Nat := 118140960795 + 886270 * 2 ^ 59
def prefixEnd_886270 : Nat := 4983230072969 + 3 ^ 40 * 886270 * 2
def baseEnd_886270 : Nat := 151694166553450899416375

theorem tailTrace_886270 : CollatzResearch.WordTrace tailWord_886270 prefixEnd_886270 151694166553450899416375 := by
  unfold tailWord_886270
  simp only [CollatzResearch.WordTrace]
  refine ⟨4040615312400328463812033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21549948332801751806997509 4040615312400328463812033)
  ·
    refine ⟨3030461484300246347859025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4040615312400328463812033 3030461484300246347859025)
    ·
      refine ⟨2272846113225184760894269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3030461484300246347859025 2272846113225184760894269)
      ·
        refine ⟨852317292459444285335351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2272846113225184760894269 852317292459444285335351)
        ·
          refine ⟨1278475938689166428003027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 852317292459444285335351 1278475938689166428003027)
          ·
            refine ⟨1917713908033749642004541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1278475938689166428003027 1917713908033749642004541)
            ·
              refine ⟨719142715512656115751703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1917713908033749642004541 719142715512656115751703)
              ·
                refine ⟨1078714073268984173627555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 719142715512656115751703 1078714073268984173627555)
                ·
                  refine ⟨1618071109903476260441333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1078714073268984173627555 1618071109903476260441333)
                  ·
                    refine ⟨151694166553450899416375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1618071109903476260441333 151694166553450899416375)
                    ·
                      rfl

theorem cell23_886270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_886270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_886270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_886270 prefixEnd_886270 := by exact prefixLift 886270
  have htrace : WordTrace (prefixWord ++ tailWord_886270) baseStart_886270 baseEnd_886270 := by
    simpa [prefixWord, tailWord_886270, baseEnd_886270] using wordTrace_append hprefix tailTrace_886270
  have hstable : (prefixWord ++ tailWord_886270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886270).length < 2 ^ (prefixWord ++ tailWord_886270).sum := by decide
  have hdescent : baseEnd_886270 < baseStart_886270 := by decide
  rcases family_descends (prefixWord ++ tailWord_886270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886273 : List Nat := [1, 2, 4, 1, 4, 1, 3, 1, 1, 1, 4]
def baseStart_886273 : Nat := 118140960795 + 886273 * 2 ^ 59
def prefixEnd_886273 : Nat := 4983230072969 + 3 ^ 40 * 886273 * 2
def baseEnd_886273 : Nat := 455084040102316186511611

theorem tailTrace_886273 : CollatzResearch.WordTrace tailWord_886273 prefixEnd_886273 455084040102316186511611 := by
  unfold tailWord_886273
  simp only [CollatzResearch.WordTrace]
  refine ⟨32325031918191759222855473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21550021278794506148570315 32325031918191759222855473)
  ·
    refine ⟨24243773938643819417141605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32325031918191759222855473 24243773938643819417141605)
    ·
      refine ⟨4545707613495716140714051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24243773938643819417141605 4545707613495716140714051)
      ·
        refine ⟨6818561420243574211071077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4545707613495716140714051 6818561420243574211071077)
        ·
          refine ⟨1278480266295670164575827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6818561420243574211071077 1278480266295670164575827)
          ·
            refine ⟨1917720399443505246863741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1278480266295670164575827 1917720399443505246863741)
            ·
              refine ⟨719145149791314467573903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1917720399443505246863741 719145149791314467573903)
              ·
                refine ⟨1078717724686971701360855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 719145149791314467573903 1078717724686971701360855)
                ·
                  refine ⟨1618076587030457552041283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1078717724686971701360855 1618076587030457552041283)
                  ·
                    refine ⟨2427114880545686328061925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1618076587030457552041283 2427114880545686328061925)
                    ·
                      refine ⟨455084040102316186511611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2427114880545686328061925 455084040102316186511611)
                      ·
                        rfl

theorem cell23_886273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 3, 1, 1, 1, 4].length) (baseStart_886273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_886273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_886273 prefixEnd_886273 := by exact prefixLift 886273
  have htrace : WordTrace (prefixWord ++ tailWord_886273) baseStart_886273 baseEnd_886273 := by
    simpa [prefixWord, tailWord_886273, baseEnd_886273] using wordTrace_append hprefix tailTrace_886273
  have hstable : (prefixWord ++ tailWord_886273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886273).length < 2 ^ (prefixWord ++ tailWord_886273).sum := by decide
  have hdescent : baseEnd_886273 < baseStart_886273 := by decide
  rcases family_descends (prefixWord ++ tailWord_886273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886296 : List Nat := [2, 1, 2, 3, 5, 1, 1, 8]
def baseStart_886296 : Nat := 118140960795 + 886296 * 2 ^ 59
def prefixEnd_886296 : Nat := 4983230072969 + 3 ^ 40 * 886296 * 2
def baseEnd_886296 : Nat := 16855401857680355426815

theorem tailTrace_886296 : CollatzResearch.WordTrace tailWord_886296 prefixEnd_886296 16855401857680355426815 := by
  unfold tailWord_886296
  simp only [CollatzResearch.WordTrace]
  refine ⟨16162935398554217075471371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21550580531405622767295161 16162935398554217075471371)
  ·
    refine ⟨24244403097831325613207057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16162935398554217075471371 24244403097831325613207057)
    ·
      refine ⟨18183302323373494209905293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24244403097831325613207057 18183302323373494209905293)
      ·
        refine ⟨6818738371265060328714485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18183302323373494209905293 6818738371265060328714485)
        ·
          refine ⟨639256722306099405816983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6818738371265060328714485 639256722306099405816983)
          ·
            refine ⟨958885083459149108725475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 639256722306099405816983 958885083459149108725475)
            ·
              refine ⟨1438327625188723663088213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 958885083459149108725475 1438327625188723663088213)
              ·
                refine ⟨16855401857680355426815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1438327625188723663088213 16855401857680355426815)
                ·
                  rfl

theorem cell23_886296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 8].length) (baseStart_886296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_886296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_886296 prefixEnd_886296 := by exact prefixLift 886296
  have htrace : WordTrace (prefixWord ++ tailWord_886296) baseStart_886296 baseEnd_886296 := by
    simpa [prefixWord, tailWord_886296, baseEnd_886296] using wordTrace_append hprefix tailTrace_886296
  have hstable : (prefixWord ++ tailWord_886296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886296).length < 2 ^ (prefixWord ++ tailWord_886296).sum := by decide
  have hdescent : baseEnd_886296 < baseStart_886296 := by decide
  rcases family_descends (prefixWord ++ tailWord_886296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886322 : List Nat := [3, 2, 1, 1, 2, 1, 1, 1, 3, 8]
def baseStart_886322 : Nat := 118140960795 + 886322 * 2 ^ 59
def prefixEnd_886322 : Nat := 4983230072969 + 3 ^ 40 * 886322 * 2
def baseEnd_886322 : Nat := 151703066884795498266295

theorem tailTrace_886322 : CollatzResearch.WordTrace tailWord_886322 prefixEnd_886322 151703066884795498266295 := by
  unfold tailWord_886322
  simp only [CollatzResearch.WordTrace]
  refine ⟨8081704773753560147847305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21551212730009493727592813 8081704773753560147847305)
  ·
    refine ⟨6061278580315170110885479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8081704773753560147847305 6061278580315170110885479)
    ·
      refine ⟨9091917870472755166328219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6061278580315170110885479 9091917870472755166328219)
      ·
        refine ⟨13637876805709132749492329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9091917870472755166328219 13637876805709132749492329)
        ·
          refine ⟨10228407604281849562119247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13637876805709132749492329 10228407604281849562119247)
          ·
            refine ⟨15342611406422774343178871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10228407604281849562119247 15342611406422774343178871)
            ·
              refine ⟨23013917109634161514768307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15342611406422774343178871 23013917109634161514768307)
              ·
                refine ⟨34520875664451242272152461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23013917109634161514768307 34520875664451242272152461)
                ·
                  refine ⟨12945328374169215852057173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34520875664451242272152461 12945328374169215852057173)
                  ·
                    refine ⟨151703066884795498266295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 12945328374169215852057173 151703066884795498266295)
                    ·
                      rfl

theorem cell23_886322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 3, 8].length) (baseStart_886322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_886322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_886322 prefixEnd_886322 := by exact prefixLift 886322
  have htrace : WordTrace (prefixWord ++ tailWord_886322) baseStart_886322 baseEnd_886322 := by
    simpa [prefixWord, tailWord_886322, baseEnd_886322] using wordTrace_append hprefix tailTrace_886322
  have hstable : (prefixWord ++ tailWord_886322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886322).length < 2 ^ (prefixWord ++ tailWord_886322).sum := by decide
  have hdescent : baseEnd_886322 < baseStart_886322 := by decide
  rcases family_descends (prefixWord ++ tailWord_886322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886359 : List Nat := [1, 1, 3, 2, 2, 3, 2, 1, 2, 2, 4]
def baseStart_886359 : Nat := 118140960795 + 886359 * 2 ^ 59
def prefixEnd_886359 : Nat := 4983230072969 + 3 ^ 40 * 886359 * 2
def baseEnd_886359 : Nat := 455128199438602850036215

theorem tailTrace_886359 : CollatzResearch.WordTrace tailWord_886359 prefixEnd_886359 455128199438602850036215 := by
  unfold tailWord_886359
  simp only [CollatzResearch.WordTrace]
  refine ⟨32328168595880195910486131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21552112397253463940324087 32328168595880195910486131)
  ·
    refine ⟨48492252893820293865729197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32328168595880195910486131 48492252893820293865729197)
    ·
      refine ⟨18184594835182610199648449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48492252893820293865729197 18184594835182610199648449)
      ·
        refine ⟨13638446126386957649736337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18184594835182610199648449 13638446126386957649736337)
        ·
          refine ⟨10228834594790218237302253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13638446126386957649736337 10228834594790218237302253)
          ·
            refine ⟨3835812973046331838988345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10228834594790218237302253 3835812973046331838988345)
            ·
              refine ⟨2876859729784748879241259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3835812973046331838988345 2876859729784748879241259)
              ·
                refine ⟨4315289594677123318861889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2876859729784748879241259 4315289594677123318861889)
                ·
                  refine ⟨3236467196007842489146417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4315289594677123318861889 3236467196007842489146417)
                  ·
                    refine ⟨2427350397005881866859813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3236467196007842489146417 2427350397005881866859813)
                    ·
                      refine ⟨455128199438602850036215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2427350397005881866859813 455128199438602850036215)
                      ·
                        rfl

theorem cell23_886359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_886359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_886359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_886359 prefixEnd_886359 := by exact prefixLift 886359
  have htrace : WordTrace (prefixWord ++ tailWord_886359) baseStart_886359 baseEnd_886359 := by
    simpa [prefixWord, tailWord_886359, baseEnd_886359] using wordTrace_append hprefix tailTrace_886359
  have hstable : (prefixWord ++ tailWord_886359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886359).length < 2 ^ (prefixWord ++ tailWord_886359).sum := by decide
  have hdescent : baseEnd_886359 < baseStart_886359 := by decide
  rcases family_descends (prefixWord ++ tailWord_886359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886362 : List Nat := [3, 1, 1, 2, 1, 1, 1, 2, 1, 1, 9]
def baseStart_886362 : Nat := 118140960795 + 886362 * 2 ^ 59
def prefixEnd_886362 : Nat := 4983230072969 + 3 ^ 40 * 886362 * 2
def baseEnd_886362 : Nat := 455129739880566338298701

theorem tailTrace_886362 : CollatzResearch.WordTrace tailWord_886362 prefixEnd_886362 455129739880566338298701 := by
  unfold tailWord_886362
  simp only [CollatzResearch.WordTrace]
  refine ⟨8082069503717331855711335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21552185343246218281896893 8082069503717331855711335)
  ·
    refine ⟨12123104255575997783567003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8082069503717331855711335 12123104255575997783567003)
    ·
      refine ⟨18184656383363996675350505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12123104255575997783567003 18184656383363996675350505)
      ·
        refine ⟨13638492287522997506512879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18184656383363996675350505 13638492287522997506512879)
        ·
          refine ⟨20457738431284496259769319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13638492287522997506512879 20457738431284496259769319)
          ·
            refine ⟨30686607646926744389653979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20457738431284496259769319 30686607646926744389653979)
            ·
              refine ⟨46029911470390116584480969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30686607646926744389653979 46029911470390116584480969)
              ·
                refine ⟨34522433602792587438360727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46029911470390116584480969 34522433602792587438360727)
                ·
                  refine ⟨51783650404188881157541091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34522433602792587438360727 51783650404188881157541091)
                  ·
                    refine ⟨77675475606283321736311637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51783650404188881157541091 77675475606283321736311637)
                    ·
                      refine ⟨455129739880566338298701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 77675475606283321736311637 455129739880566338298701)
                      ·
                        rfl

theorem cell23_886362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_886362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_886362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_886362 prefixEnd_886362 := by exact prefixLift 886362
  have htrace : WordTrace (prefixWord ++ tailWord_886362) baseStart_886362 baseEnd_886362 := by
    simpa [prefixWord, tailWord_886362, baseEnd_886362] using wordTrace_append hprefix tailTrace_886362
  have hstable : (prefixWord ++ tailWord_886362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886362).length < 2 ^ (prefixWord ++ tailWord_886362).sum := by decide
  have hdescent : baseEnd_886362 < baseStart_886362 := by decide
  rcases family_descends (prefixWord ++ tailWord_886362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886436 : List Nat := [2, 3, 1, 2, 2, 2, 1, 3, 2, 1, 4]
def baseStart_886436 : Nat := 118140960795 + 886436 * 2 ^ 59
def prefixEnd_886436 : Nat := 4983230072969 + 3 ^ 40 * 886436 * 2
def baseEnd_886436 : Nat := 455167737448999048773361

theorem tailTrace_886436 : CollatzResearch.WordTrace tailWord_886436 prefixEnd_886436 455167737448999048773361 := by
  unfold tailWord_886436
  simp only [CollatzResearch.WordTrace]
  refine ⟨16165488508300619030519581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21553984677734158707359441 16165488508300619030519581)
  ·
    refine ⟨6062058190612732136444843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16165488508300619030519581 6062058190612732136444843)
    ·
      refine ⟨9093087285919098204667265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6062058190612732136444843 9093087285919098204667265)
      ·
        refine ⟨6819815464439323653500449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9093087285919098204667265 6819815464439323653500449)
        ·
          refine ⟨5114861598329492740125337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6819815464439323653500449 5114861598329492740125337)
          ·
            refine ⟨3836146198747119555094003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5114861598329492740125337 3836146198747119555094003)
            ·
              refine ⟨5754219298120679332641005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3836146198747119555094003 5754219298120679332641005)
              ·
                refine ⟨2157832236795254749740377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5754219298120679332641005 2157832236795254749740377)
                ·
                  refine ⟨1618374177596441062305283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2157832236795254749740377 1618374177596441062305283)
                  ·
                    refine ⟨2427561266394661593457925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1618374177596441062305283 2427561266394661593457925)
                    ·
                      refine ⟨455167737448999048773361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2427561266394661593457925 455167737448999048773361)
                      ·
                        rfl

theorem cell23_886436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_886436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_886436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_886436 prefixEnd_886436 := by exact prefixLift 886436
  have htrace : WordTrace (prefixWord ++ tailWord_886436) baseStart_886436 baseEnd_886436 := by
    simpa [prefixWord, tailWord_886436, baseEnd_886436] using wordTrace_append hprefix tailTrace_886436
  have hstable : (prefixWord ++ tailWord_886436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886436).length < 2 ^ (prefixWord ++ tailWord_886436).sum := by decide
  have hdescent : baseEnd_886436 < baseStart_886436 := by decide
  rcases family_descends (prefixWord ++ tailWord_886436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886463 : List Nat := [1, 1, 2, 2, 2, 3, 3, 4, 1, 4]
def baseStart_886463 : Nat := 118140960795 + 886463 * 2 ^ 59
def prefixEnd_886463 : Nat := 4983230072969 + 3 ^ 40 * 886463 * 2
def baseEnd_886463 : Nat := 151727200475556814378579

theorem tailTrace_886463 : CollatzResearch.WordTrace tailWord_886463 prefixEnd_886463 151727200475556814378579 := by
  unfold tailWord_886463
  simp only [CollatzResearch.WordTrace]
  refine ⟨32331961787503421672272043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21554641191668947781514695 32331961787503421672272043)
  ·
    refine ⟨48497942681255132508408065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32331961787503421672272043 48497942681255132508408065)
    ·
      refine ⟨36373457010941349381306049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48497942681255132508408065 36373457010941349381306049)
      ·
        refine ⟨27280092758206012035979537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36373457010941349381306049 27280092758206012035979537)
        ·
          refine ⟨20460069568654509026984653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27280092758206012035979537 20460069568654509026984653)
          ·
            refine ⟨7672526088245440885119245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20460069568654509026984653 7672526088245440885119245)
            ·
              refine ⟨2877197283092040331919717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7672526088245440885119245 2877197283092040331919717)
              ·
                refine ⟨539474490579757562234947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2877197283092040331919717 539474490579757562234947)
                ·
                  refine ⟨809211735869636343352421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 539474490579757562234947 809211735869636343352421)
                  ·
                    refine ⟨151727200475556814378579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 809211735869636343352421 151727200475556814378579)
                    ·
                      rfl

theorem cell23_886463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 4, 1, 4].length) (baseStart_886463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_886463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_886463 prefixEnd_886463 := by exact prefixLift 886463
  have htrace : WordTrace (prefixWord ++ tailWord_886463) baseStart_886463 baseEnd_886463 := by
    simpa [prefixWord, tailWord_886463, baseEnd_886463] using wordTrace_append hprefix tailTrace_886463
  have hstable : (prefixWord ++ tailWord_886463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886463).length < 2 ^ (prefixWord ++ tailWord_886463).sum := by decide
  have hdescent : baseEnd_886463 < baseStart_886463 := by decide
  rcases family_descends (prefixWord ++ tailWord_886463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886519 : List Nat := [1, 1, 3, 1, 1, 1, 4, 2, 3, 6]
def baseStart_886519 : Nat := 118140960795 + 886519 * 2 ^ 59
def prefixEnd_886519 : Nat := 4983230072969 + 3 ^ 40 * 886519 * 2
def baseEnd_886519 : Nat := 151736785447774074678493

theorem tailTrace_886519 : CollatzResearch.WordTrace tailWord_886519 prefixEnd_886519 151736785447774074678493 := by
  unfold tailWord_886519
  simp only [CollatzResearch.WordTrace]
  refine ⟨32334004275300543236310611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21556002850200362157540407 32334004275300543236310611)
  ·
    refine ⟨48501006412950814854465917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32334004275300543236310611 48501006412950814854465917)
    ·
      refine ⟨18187877404856555570424719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48501006412950814854465917 18187877404856555570424719)
      ·
        refine ⟨27281816107284833355637079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18187877404856555570424719 27281816107284833355637079)
        ·
          refine ⟨40922724160927250033455619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27281816107284833355637079 40922724160927250033455619)
          ·
            refine ⟨61384086241390875050183429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40922724160927250033455619 61384086241390875050183429)
            ·
              refine ⟨11509516170260789071909393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61384086241390875050183429 11509516170260789071909393)
              ·
                refine ⟨8632137127695591803932045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11509516170260789071909393 8632137127695591803932045)
                ·
                  refine ⟨3237051422885846926474517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8632137127695591803932045 3237051422885846926474517)
                  ·
                    refine ⟨151736785447774074678493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3237051422885846926474517 151736785447774074678493)
                    ·
                      rfl

theorem cell23_886519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 3, 6].length) (baseStart_886519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_886519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_886519 prefixEnd_886519 := by exact prefixLift 886519
  have htrace : WordTrace (prefixWord ++ tailWord_886519) baseStart_886519 baseEnd_886519 := by
    simpa [prefixWord, tailWord_886519, baseEnd_886519] using wordTrace_append hprefix tailTrace_886519
  have hstable : (prefixWord ++ tailWord_886519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886519).length < 2 ^ (prefixWord ++ tailWord_886519).sum := by decide
  have hdescent : baseEnd_886519 < baseStart_886519 := by decide
  rcases family_descends (prefixWord ++ tailWord_886519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886543 : List Nat := [1, 1, 2, 1, 1, 1, 4, 3, 5, 2, 2]
def baseStart_886543 : Nat := 118140960795 + 886543 * 2 ^ 59
def prefixEnd_886543 : Nat := 4983230072969 + 3 ^ 40 * 886543 * 2
def baseEnd_886543 : Nat := 455222679879030130135369

theorem tailTrace_886543 : CollatzResearch.WordTrace tailWord_886543 prefixEnd_886543 455222679879030130135369 := by
  unfold tailWord_886543
  simp only [CollatzResearch.WordTrace]
  refine ⟨32334879627213595335184283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21556586418142396890122855 32334879627213595335184283)
  ·
    refine ⟨48502319440820393002776425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32334879627213595335184283 48502319440820393002776425)
    ·
      refine ⟨36376739580615294752082319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48502319440820393002776425 36376739580615294752082319)
      ·
        refine ⟨54565109370922942128123479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36376739580615294752082319 54565109370922942128123479)
        ·
          refine ⟨81847664056384413192185219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54565109370922942128123479 81847664056384413192185219)
          ·
            refine ⟨122771496084576619788277829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81847664056384413192185219 122771496084576619788277829)
            ·
              refine ⟨23019655515858116210302093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122771496084576619788277829 23019655515858116210302093)
              ·
                refine ⟨8632370818446793578863285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23019655515858116210302093 8632370818446793578863285)
                ·
                  refine ⟨809284764229386898018433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8632370818446793578863285 809284764229386898018433)
                  ·
                    refine ⟨606963573172040173513825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 809284764229386898018433 606963573172040173513825)
                    ·
                      refine ⟨455222679879030130135369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 606963573172040173513825 455222679879030130135369)
                      ·
                        rfl

theorem cell23_886543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 5, 2, 2].length) (baseStart_886543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_886543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_886543 prefixEnd_886543 := by exact prefixLift 886543
  have htrace : WordTrace (prefixWord ++ tailWord_886543) baseStart_886543 baseEnd_886543 := by
    simpa [prefixWord, tailWord_886543, baseEnd_886543] using wordTrace_append hprefix tailTrace_886543
  have hstable : (prefixWord ++ tailWord_886543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886543).length < 2 ^ (prefixWord ++ tailWord_886543).sum := by decide
  have hdescent : baseEnd_886543 < baseStart_886543 := by decide
  rcases family_descends (prefixWord ++ tailWord_886543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886548 : List Nat := [2, 4, 4, 1, 2, 1, 1, 3, 1, 4]
def baseStart_886548 : Nat := 118140960795 + 886548 * 2 ^ 59
def prefixEnd_886548 : Nat := 4983230072969 + 3 ^ 40 * 886548 * 2
def baseEnd_886548 : Nat := 151741749094100870190949

theorem tailTrace_886548 : CollatzResearch.WordTrace tailWord_886548 prefixEnd_886548 151741749094100870190949 := by
  unfold tailWord_886548
  simp only [CollatzResearch.WordTrace]
  refine ⟨16167530996097740594558149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21556707994796987459410865 16167530996097740594558149)
  ·
    refine ⟨3031412061768326361479653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16167530996097740594558149 3031412061768326361479653)
    ·
      refine ⟨568389761581561192777435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3031412061768326361479653 568389761581561192777435)
      ·
        refine ⟨852584642372341789166153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 568389761581561192777435 852584642372341789166153)
        ·
          refine ⟨639438481779256341874615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 852584642372341789166153 639438481779256341874615)
          ·
            refine ⟨959157722668884512811923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 639438481779256341874615 959157722668884512811923)
            ·
              refine ⟨1438736584003326769217885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 959157722668884512811923 1438736584003326769217885)
              ·
                refine ⟨539526219001247538456707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1438736584003326769217885 539526219001247538456707)
                ·
                  refine ⟨809289328501871307685061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 539526219001247538456707 809289328501871307685061)
                  ·
                    refine ⟨151741749094100870190949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 809289328501871307685061 151741749094100870190949)
                    ·
                      rfl

theorem cell23_886548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_886548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_886548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_886548 prefixEnd_886548 := by exact prefixLift 886548
  have htrace : WordTrace (prefixWord ++ tailWord_886548) baseStart_886548 baseEnd_886548 := by
    simpa [prefixWord, tailWord_886548, baseEnd_886548] using wordTrace_append hprefix tailTrace_886548
  have hstable : (prefixWord ++ tailWord_886548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886548).length < 2 ^ (prefixWord ++ tailWord_886548).sum := by decide
  have hdescent : baseEnd_886548 < baseStart_886548 := by decide
  rcases family_descends (prefixWord ++ tailWord_886548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886556 : List Nat := [2, 2, 3, 1, 1, 2, 2, 1, 3, 2, 4]
def baseStart_886556 : Nat := 118140960795 + 886556 * 2 ^ 59
def prefixEnd_886556 : Nat := 4983230072969 + 3 ^ 40 * 886556 * 2
def baseEnd_886556 : Nat := 455229355127538579272809

theorem tailTrace_886556 : CollatzResearch.WordTrace tailWord_886556 prefixEnd_886556 455229355127538579272809 := by
  unfold tailWord_886556
  simp only [CollatzResearch.WordTrace]
  refine ⟨16167676888083249277703761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21556902517444332370271681 16167676888083249277703761)
  ·
    refine ⟨12125757666062436958277821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16167676888083249277703761 12125757666062436958277821)
    ·
      refine ⟨4547159124773413859354183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12125757666062436958277821 4547159124773413859354183)
      ·
        refine ⟨6820738687160120789031275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4547159124773413859354183 6820738687160120789031275)
        ·
          refine ⟨10231108030740181183546913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6820738687160120789031275 10231108030740181183546913)
          ·
            refine ⟨7673331023055135887660185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10231108030740181183546913 7673331023055135887660185)
            ·
              refine ⟨5754998267291351915745139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7673331023055135887660185 5754998267291351915745139)
              ·
                refine ⟨8632497400937027873617709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5754998267291351915745139 8632497400937027873617709)
                ·
                  refine ⟨3237186525351385452606641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8632497400937027873617709 3237186525351385452606641)
                  ·
                    refine ⟨2427889894013539089454981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3237186525351385452606641 2427889894013539089454981)
                    ·
                      refine ⟨455229355127538579272809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2427889894013539089454981 455229355127538579272809)
                      ·
                        rfl

theorem cell23_886556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_886556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_886556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_886556 prefixEnd_886556 := by exact prefixLift 886556
  have htrace : WordTrace (prefixWord ++ tailWord_886556) baseStart_886556 baseEnd_886556 := by
    simpa [prefixWord, tailWord_886556, baseEnd_886556] using wordTrace_append hprefix tailTrace_886556
  have hstable : (prefixWord ++ tailWord_886556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886556).length < 2 ^ (prefixWord ++ tailWord_886556).sum := by decide
  have hdescent : baseEnd_886556 < baseStart_886556 := by decide
  rcases family_descends (prefixWord ++ tailWord_886556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886563 : List Nat := [1, 1, 1, 4, 2, 1, 4, 3, 1, 2, 3]
def baseStart_886563 : Nat := 118140960795 + 886563 * 2 ^ 59
def prefixEnd_886563 : Nat := 4983230072969 + 3 ^ 40 * 886563 * 2
def baseEnd_886563 : Nat := 455232949492120051885277

theorem tailTrace_886563 : CollatzResearch.WordTrace tailWord_886563 prefixEnd_886563 455232949492120051885277 := by
  unfold tailWord_886563
  simp only [CollatzResearch.WordTrace]
  refine ⟨32335609087141138750912343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21557072724760759167274895 32335609087141138750912343)
  ·
    refine ⟨48503413630711708126368515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32335609087141138750912343 48503413630711708126368515)
    ·
      refine ⟨72755120446067562189552773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48503413630711708126368515 72755120446067562189552773)
      ·
        refine ⟨13641585083637667910541145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72755120446067562189552773 13641585083637667910541145)
        ·
          refine ⟨10231188812728250932905859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13641585083637667910541145 10231188812728250932905859)
          ·
            refine ⟨15346783219092376399358789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10231188812728250932905859 15346783219092376399358789)
            ·
              refine ⟨2877521853579820574879773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15346783219092376399358789 2877521853579820574879773)
              ·
                refine ⟨1079070695092432715579915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2877521853579820574879773 1079070695092432715579915)
                ·
                  refine ⟨1618606042638649073369873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1079070695092432715579915 1618606042638649073369873)
                  ·
                    refine ⟨1213954531978986805027405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1618606042638649073369873 1213954531978986805027405)
                    ·
                      refine ⟨455232949492120051885277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1213954531978986805027405 455232949492120051885277)
                      ·
                        rfl

theorem cell23_886563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 3, 1, 2, 3].length) (baseStart_886563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_886563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_886563 prefixEnd_886563 := by exact prefixLift 886563
  have htrace : WordTrace (prefixWord ++ tailWord_886563) baseStart_886563 baseEnd_886563 := by
    simpa [prefixWord, tailWord_886563, baseEnd_886563] using wordTrace_append hprefix tailTrace_886563
  have hstable : (prefixWord ++ tailWord_886563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886563).length < 2 ^ (prefixWord ++ tailWord_886563).sum := by decide
  have hdescent : baseEnd_886563 < baseStart_886563 := by decide
  rcases family_descends (prefixWord ++ tailWord_886563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
