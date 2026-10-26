import V185TrunkScan23Chunk0885

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5243849 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 1, 2, 9]
def baseStart_5243849 : Nat := 118140960795 + 5243849 * 2 ^ 59
def prefixEnd_5243849 : Nat := 4983230072969 + 3 ^ 40 * 5243849 * 2
def baseEnd_5243849 : Nat := 2692615016598759150371483

theorem tailTrace_5243849 : CollatzResearch.WordTrace tailWord_5243849 prefixEnd_5243849 2692615016598759150371483 := by
  unfold tailWord_5243849
  simp only [CollatzResearch.WordTrace]
  refine ⟨191258885579438125953694601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127505923719625417302463067 191258885579438125953694601)
  ·
    refine ⟨143444164184578594465270951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191258885579438125953694601 143444164184578594465270951)
    ·
      refine ⟨215166246276867891697906427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143444164184578594465270951 215166246276867891697906427)
      ·
        refine ⟨322749369415301837546859641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215166246276867891697906427 322749369415301837546859641)
        ·
          refine ⟨242062027061476378160144731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 322749369415301837546859641 242062027061476378160144731)
          ·
            refine ⟨363093040592214567240217097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242062027061476378160144731 363093040592214567240217097)
            ·
              refine ⟨272319780444160925430162823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 363093040592214567240217097 272319780444160925430162823)
              ·
                refine ⟨408479670666241388145244235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 272319780444160925430162823 408479670666241388145244235)
                ·
                  refine ⟨612719505999362082217866353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 408479670666241388145244235 612719505999362082217866353)
                  ·
                    refine ⟨459539629499521561663399765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 612719505999362082217866353 459539629499521561663399765)
                    ·
                      refine ⟨2692615016598759150371483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 459539629499521561663399765 2692615016598759150371483)
                      ·
                        rfl

theorem cell23_5243849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 2, 9].length) (baseStart_5243849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5243849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5243849 prefixEnd_5243849 := by exact prefixLift 5243849
  have htrace : WordTrace (prefixWord ++ tailWord_5243849) baseStart_5243849 baseEnd_5243849 := by
    simpa [prefixWord, tailWord_5243849, baseEnd_5243849] using wordTrace_append hprefix tailTrace_5243849
  have hstable : (prefixWord ++ tailWord_5243849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5243849).length < 2 ^ (prefixWord ++ tailWord_5243849).sum := by decide
  have hdescent : baseEnd_5243849 < baseStart_5243849 := by decide
  rcases family_descends (prefixWord ++ tailWord_5243849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5243856 : List Nat := [2, 1, 1, 1, 1, 2, 3, 1, 7, 4]
def baseStart_5243856 : Nat := 118140960795 + 5243856 * 2 ^ 59
def prefixEnd_5243856 : Nat := 4983230072969 + 3 ^ 40 * 5243856 * 2
def baseEnd_5243856 : Nat := 897539536987780207661317

theorem tailTrace_5243856 : CollatzResearch.WordTrace tailWord_5243856 prefixEnd_5243856 897539536987780207661317 := by
  unfold tailWord_5243856
  simp only [CollatzResearch.WordTrace]
  refine ⟨95629570445206383074599711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127506093926941844099466281 95629570445206383074599711)
  ·
    refine ⟨143444355667809574611899567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95629570445206383074599711 143444355667809574611899567)
    ·
      refine ⟨215166533501714361917849351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143444355667809574611899567 215166533501714361917849351)
      ·
        refine ⟨322749800252571542876774027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215166533501714361917849351 322749800252571542876774027)
        ·
          refine ⟨484124700378857314315161041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322749800252571542876774027 484124700378857314315161041)
          ·
            refine ⟨363093525284142985736370781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 484124700378857314315161041 363093525284142985736370781)
            ·
              refine ⟨136160071981553619651139043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 363093525284142985736370781 136160071981553619651139043)
              ·
                refine ⟨204240107972330429476708565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136160071981553619651139043 204240107972330429476708565)
                ·
                  refine ⟨4786877530601494440860357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 204240107972330429476708565 4786877530601494440860357)
                  ·
                    refine ⟨897539536987780207661317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4786877530601494440860357 897539536987780207661317)
                    ·
                      rfl

theorem cell23_5243856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 7, 4].length) (baseStart_5243856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5243856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5243856 prefixEnd_5243856 := by exact prefixLift 5243856
  have htrace : WordTrace (prefixWord ++ tailWord_5243856) baseStart_5243856 baseEnd_5243856 := by
    simpa [prefixWord, tailWord_5243856, baseEnd_5243856] using wordTrace_append hprefix tailTrace_5243856
  have hstable : (prefixWord ++ tailWord_5243856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5243856).length < 2 ^ (prefixWord ++ tailWord_5243856).sum := by decide
  have hdescent : baseEnd_5243856 < baseStart_5243856 := by decide
  rcases family_descends (prefixWord ++ tailWord_5243856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5243896 : List Nat := [2, 1, 2, 1, 1, 3, 1, 1, 1, 7, 3]
def baseStart_5243896 : Nat := 118140960795 + 5243896 * 2 ^ 59
def prefixEnd_5243896 : Nat := 4983230072969 + 3 ^ 40 * 5243896 * 2
def baseEnd_5243896 : Nat := 2692639150189520466483767

theorem tailTrace_5243896 : CollatzResearch.WordTrace tailWord_5243896 prefixEnd_5243896 2692639150189520466483767 := by
  unfold tailWord_5243896
  simp only [CollatzResearch.WordTrace]
  refine ⟨95630299905133926490327771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127507066540178568653770361 95630299905133926490327771)
  ·
    refine ⟨143445449857700889735491657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95630299905133926490327771 143445449857700889735491657)
    ·
      refine ⟨107584087393275667301618743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143445449857700889735491657 107584087393275667301618743)
      ·
        refine ⟨161376131089913500952428115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107584087393275667301618743 161376131089913500952428115)
        ·
          refine ⟨242064196634870251428642173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161376131089913500952428115 242064196634870251428642173)
          ·
            refine ⟨90774073738076344285740815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 242064196634870251428642173 90774073738076344285740815)
            ·
              refine ⟨136161110607114516428611223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90774073738076344285740815 136161110607114516428611223)
              ·
                refine ⟨204241665910671774642916835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136161110607114516428611223 204241665910671774642916835)
                ·
                  refine ⟨306362498866007661964375253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 204241665910671774642916835 306362498866007661964375253)
                  ·
                    refine ⟨7180371067172054577290045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 306362498866007661964375253 7180371067172054577290045)
                    ·
                      refine ⟨2692639150189520466483767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7180371067172054577290045 2692639150189520466483767)
                      ·
                        rfl

theorem cell23_5243896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 1, 7, 3].length) (baseStart_5243896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5243896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5243896 prefixEnd_5243896 := by exact prefixLift 5243896
  have htrace : WordTrace (prefixWord ++ tailWord_5243896) baseStart_5243896 baseEnd_5243896 := by
    simpa [prefixWord, tailWord_5243896, baseEnd_5243896] using wordTrace_append hprefix tailTrace_5243896
  have hstable : (prefixWord ++ tailWord_5243896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5243896).length < 2 ^ (prefixWord ++ tailWord_5243896).sum := by decide
  have hdescent : baseEnd_5243896 < baseStart_5243896 := by decide
  rcases family_descends (prefixWord ++ tailWord_5243896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5243913 : List Nat := [1, 2, 1, 1, 3, 1, 1, 4, 5, 1, 3]
def baseStart_5243913 : Nat := 118140960795 + 5243913 * 2 ^ 59
def prefixEnd_5243913 : Nat := 4983230072969 + 3 ^ 40 * 5243913 * 2
def baseEnd_5243913 : Nat := 2692647879360646899971189

theorem tailTrace_5243913 : CollatzResearch.WordTrace tailWord_5243913 prefixEnd_5243913 2692647879360646899971189 := by
  unfold tailWord_5243913
  simp only [CollatzResearch.WordTrace]
  refine ⟨191261219851206264884024393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127507479900804176589349595 191261219851206264884024393)
  ·
    refine ⟨143445914888404698663018295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191261219851206264884024393 143445914888404698663018295)
    ·
      refine ⟨215168872332607047994527443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143445914888404698663018295 215168872332607047994527443)
      ·
        refine ⟨322753308498910571991791165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215168872332607047994527443 322753308498910571991791165)
        ·
          refine ⟨121032490687091464496921687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 322753308498910571991791165 121032490687091464496921687)
          ·
            refine ⟨181548736030637196745382531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121032490687091464496921687 181548736030637196745382531)
            ·
              refine ⟨272323104045955795118073797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181548736030637196745382531 272323104045955795118073797)
              ·
                refine ⟨51060582008616711584638837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 272323104045955795118073797 51060582008616711584638837)
                ·
                  refine ⟨4786929563307816711059891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51060582008616711584638837 4786929563307816711059891)
                  ·
                    refine ⟨7180394344961725066589837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4786929563307816711059891 7180394344961725066589837)
                    ·
                      refine ⟨2692647879360646899971189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7180394344961725066589837 2692647879360646899971189)
                      ·
                        rfl

theorem cell23_5243913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 5, 1, 3].length) (baseStart_5243913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5243913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5243913 prefixEnd_5243913 := by exact prefixLift 5243913
  have htrace : WordTrace (prefixWord ++ tailWord_5243913) baseStart_5243913 baseEnd_5243913 := by
    simpa [prefixWord, tailWord_5243913, baseEnd_5243913] using wordTrace_append hprefix tailTrace_5243913
  have hstable : (prefixWord ++ tailWord_5243913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5243913).length < 2 ^ (prefixWord ++ tailWord_5243913).sum := by decide
  have hdescent : baseEnd_5243913 < baseStart_5243913 := by decide
  rcases family_descends (prefixWord ++ tailWord_5243913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5243953 : List Nat := [1, 2, 2, 3, 1, 2, 3, 1, 3, 1, 4]
def baseStart_5243953 : Nat := 118140960795 + 5243953 * 2 ^ 59
def prefixEnd_5243953 : Nat := 4983230072969 + 3 ^ 40 * 5243953 * 2
def baseEnd_5243953 : Nat := 2692668418586826743471005

theorem tailTrace_5243953 : CollatzResearch.WordTrace tailWord_5243953 prefixEnd_5243953 2692668418586826743471005 := by
  unfold tailWord_5243953
  simp only [CollatzResearch.WordTrace]
  refine ⟨191262678771061351715480513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127508452514040901143653675 191262678771061351715480513)
  ·
    refine ⟨143447009078296013786610385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191262678771061351715480513 143447009078296013786610385)
    ·
      refine ⟨107585256808722010339957789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143447009078296013786610385 107585256808722010339957789)
      ·
        refine ⟨40344471303270753877484171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107585256808722010339957789 40344471303270753877484171)
        ·
          refine ⟨60516706954906130816226257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40344471303270753877484171 60516706954906130816226257)
          ·
            refine ⟨45387530216179598112169693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60516706954906130816226257 45387530216179598112169693)
            ·
              refine ⟨17020323831067349292063635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45387530216179598112169693 17020323831067349292063635)
              ·
                refine ⟨25530485746601023938095453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17020323831067349292063635 25530485746601023938095453)
                ·
                  refine ⟨9573932154975383976785795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25530485746601023938095453 9573932154975383976785795)
                  ·
                    refine ⟨14360898232463075965178693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9573932154975383976785795 14360898232463075965178693)
                    ·
                      refine ⟨2692668418586826743471005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14360898232463075965178693 2692668418586826743471005)
                      ·
                        rfl

theorem cell23_5243953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_5243953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5243953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5243953 prefixEnd_5243953 := by exact prefixLift 5243953
  have htrace : WordTrace (prefixWord ++ tailWord_5243953) baseStart_5243953 baseEnd_5243953 := by
    simpa [prefixWord, tailWord_5243953, baseEnd_5243953] using wordTrace_append hprefix tailTrace_5243953
  have hstable : (prefixWord ++ tailWord_5243953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5243953).length < 2 ^ (prefixWord ++ tailWord_5243953).sum := by decide
  have hdescent : baseEnd_5243953 < baseStart_5243953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5243953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5243973 : List Nat := [1, 3, 1, 1, 1, 3, 5, 1, 1, 1, 5]
def baseStart_5243973 : Nat := 118140960795 + 5243973 * 2 ^ 59
def prefixEnd_5243973 : Nat := 4983230072969 + 3 ^ 40 * 5243973 * 2
def baseEnd_5243973 : Nat := 2692678688199916665220913

theorem tailTrace_5243973 : CollatzResearch.WordTrace tailWord_5243973 prefixEnd_5243973 2692678688199916665220913 := by
  unfold tailWord_5243973
  simp only [CollatzResearch.WordTrace]
  refine ⟨191263408230988895131208573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127508938820659263420805715 191263408230988895131208573)
  ·
    refine ⟨71723778086620835674203215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191263408230988895131208573 71723778086620835674203215)
    ·
      refine ⟨107585667129931253511304823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71723778086620835674203215 107585667129931253511304823)
      ·
        refine ⟨161378500694896880266957235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107585667129931253511304823 161378500694896880266957235)
        ·
          refine ⟨242067751042345320400435853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161378500694896880266957235 242067751042345320400435853)
          ·
            refine ⟨90775406640879495150163445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 242067751042345320400435853 90775406640879495150163445)
            ·
              refine ⟨8510194372582452670327823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 90775406640879495150163445 8510194372582452670327823)
              ·
                refine ⟨12765291558873679005491735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8510194372582452670327823 12765291558873679005491735)
                ·
                  refine ⟨19147937338310518508237603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12765291558873679005491735 19147937338310518508237603)
                  ·
                    refine ⟨28721906007465777762356405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19147937338310518508237603 28721906007465777762356405)
                    ·
                      refine ⟨2692678688199916665220913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28721906007465777762356405 2692678688199916665220913)
                      ·
                        rfl

theorem cell23_5243973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 1, 1, 1, 5].length) (baseStart_5243973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5243973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5243973 prefixEnd_5243973 := by exact prefixLift 5243973
  have htrace : WordTrace (prefixWord ++ tailWord_5243973) baseStart_5243973 baseEnd_5243973 := by
    simpa [prefixWord, tailWord_5243973, baseEnd_5243973] using wordTrace_append hprefix tailTrace_5243973
  have hstable : (prefixWord ++ tailWord_5243973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5243973).length < 2 ^ (prefixWord ++ tailWord_5243973).sum := by decide
  have hdescent : baseEnd_5243973 < baseStart_5243973 := by decide
  rcases family_descends (prefixWord ++ tailWord_5243973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5243974 : List Nat := [6, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2]
def baseStart_5243974 : Nat := 118140960795 + 5243974 * 2 ^ 59
def prefixEnd_5243974 : Nat := 4983230072969 + 3 ^ 40 * 5243974 * 2
def baseEnd_5243974 : Nat := 2692679201680571161308409

theorem tailTrace_5243974 : CollatzResearch.WordTrace tailWord_5243974 prefixEnd_5243974 2692679201680571161308409 := by
  unfold tailWord_5243974
  simp only [CollatzResearch.WordTrace]
  refine ⟨5976982646999539759437343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 127508963135990181534663317 5976982646999539759437343)
  ·
    refine ⟨8965473970499309639156015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5976982646999539759437343 8965473970499309639156015)
    ·
      refine ⟨13448210955748964458734023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8965473970499309639156015 13448210955748964458734023)
      ·
        refine ⟨20172316433623446688101035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13448210955748964458734023 20172316433623446688101035)
        ·
          refine ⟨30258474650435170032151553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20172316433623446688101035 30258474650435170032151553)
          ·
            refine ⟨22693855987826377524113665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30258474650435170032151553 22693855987826377524113665)
            ·
              refine ⟨17020391990869783143085249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22693855987826377524113665 17020391990869783143085249)
              ·
                refine ⟨12765293993152337357313937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17020391990869783143085249 12765293993152337357313937)
                ·
                  refine ⟨9573970494864253017985453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12765293993152337357313937 9573970494864253017985453)
                  ·
                    refine ⟨3590238935574094881744545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9573970494864253017985453 3590238935574094881744545)
                    ·
                      refine ⟨2692679201680571161308409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3590238935574094881744545 2692679201680571161308409)
                      ·
                        rfl

theorem cell23_5243974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_5243974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5243974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5243974 prefixEnd_5243974 := by exact prefixLift 5243974
  have htrace : WordTrace (prefixWord ++ tailWord_5243974) baseStart_5243974 baseEnd_5243974 := by
    simpa [prefixWord, tailWord_5243974, baseEnd_5243974] using wordTrace_append hprefix tailTrace_5243974
  have hstable : (prefixWord ++ tailWord_5243974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5243974).length < 2 ^ (prefixWord ++ tailWord_5243974).sum := by decide
  have hdescent : baseEnd_5243974 < baseStart_5243974 := by decide
  rcases family_descends (prefixWord ++ tailWord_5243974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5243981 : List Nat := [1, 6, 1, 1, 1, 2, 4, 2, 1, 1, 3]
def baseStart_5243981 : Nat := 118140960795 + 5243981 * 2 ^ 59
def prefixEnd_5243981 : Nat := 4983230072969 + 3 ^ 40 * 5243981 * 2
def baseEnd_5243981 : Nat := 2692682796045152633920877

theorem tailTrace_5243981 : CollatzResearch.WordTrace tailWord_5243981 prefixEnd_5243981 2692682796045152633920877 := by
  unfold tailWord_5243981
  simp only [CollatzResearch.WordTrace]
  refine ⟨191263700014959912497499797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127509133343306608331666531 191263700014959912497499797)
  ·
    refine ⟨8965485938201245898320303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 191263700014959912497499797 8965485938201245898320303)
    ·
      refine ⟨13448228907301868847480455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8965485938201245898320303 13448228907301868847480455)
      ·
        refine ⟨20172343360952803271220683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13448228907301868847480455 20172343360952803271220683)
        ·
          refine ⟨30258515041429204906831025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20172343360952803271220683 30258515041429204906831025)
          ·
            refine ⟨22693886281071903680123269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30258515041429204906831025 22693886281071903680123269)
            ·
              refine ⟨4255103677700981940023113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22693886281071903680123269 4255103677700981940023113)
              ·
                refine ⟨3191327758275736455017335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4255103677700981940023113 3191327758275736455017335)
                ·
                  refine ⟨4786991637413604682526003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3191327758275736455017335 4786991637413604682526003)
                  ·
                    refine ⟨7180487456120407023789005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4786991637413604682526003 7180487456120407023789005)
                    ·
                      refine ⟨2692682796045152633920877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7180487456120407023789005 2692682796045152633920877)
                      ·
                        rfl

theorem cell23_5243981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 4, 2, 1, 1, 3].length) (baseStart_5243981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5243981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5243981 prefixEnd_5243981 := by exact prefixLift 5243981
  have htrace : WordTrace (prefixWord ++ tailWord_5243981) baseStart_5243981 baseEnd_5243981 := by
    simpa [prefixWord, tailWord_5243981, baseEnd_5243981] using wordTrace_append hprefix tailTrace_5243981
  have hstable : (prefixWord ++ tailWord_5243981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5243981).length < 2 ^ (prefixWord ++ tailWord_5243981).sum := by decide
  have hdescent : baseEnd_5243981 < baseStart_5243981 := by decide
  rcases family_descends (prefixWord ++ tailWord_5243981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5243997 : List Nat := [1, 4, 4, 1, 2, 1, 2, 1, 1, 6]
def baseStart_5243997 : Nat := 118140960795 + 5243997 * 2 ^ 59
def prefixEnd_5243997 : Nat := 4983230072969 + 3 ^ 40 * 5243997 * 2
def baseEnd_5243997 : Nat := 897563670578541523773601

theorem tailTrace_5243997 : CollatzResearch.WordTrace tailWord_5243997 prefixEnd_5243997 897563670578541523773601 := by
  unfold tailWord_5243997
  simp only [CollatzResearch.WordTrace]
  refine ⟨191264283582901947230082245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127509522388601298153388163 191264283582901947230082245)
  ·
    refine ⟨35862053171794115105640421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 191264283582901947230082245 35862053171794115105640421)
    ·
      refine ⟨6724134969711396582307579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35862053171794115105640421 6724134969711396582307579)
      ·
        refine ⟨10086202454567094873461369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6724134969711396582307579 10086202454567094873461369)
        ·
          refine ⟨7564651840925321155096027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10086202454567094873461369 7564651840925321155096027)
          ·
            refine ⟨11346977761387981732644041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7564651840925321155096027 11346977761387981732644041)
            ·
              refine ⟨8510233321040986299483031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11346977761387981732644041 8510233321040986299483031)
              ·
                refine ⟨12765349981561479449224547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8510233321040986299483031 12765349981561479449224547)
                ·
                  refine ⟨19148024972342219173836821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12765349981561479449224547 19148024972342219173836821)
                  ·
                    refine ⟨897563670578541523773601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19148024972342219173836821 897563670578541523773601)
                    ·
                      rfl

theorem cell23_5243997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_5243997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5243997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5243997 prefixEnd_5243997 := by exact prefixLift 5243997
  have htrace : WordTrace (prefixWord ++ tailWord_5243997) baseStart_5243997 baseEnd_5243997 := by
    simpa [prefixWord, tailWord_5243997, baseEnd_5243997] using wordTrace_append hprefix tailTrace_5243997
  have hstable : (prefixWord ++ tailWord_5243997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5243997).length < 2 ^ (prefixWord ++ tailWord_5243997).sum := by decide
  have hdescent : baseEnd_5243997 < baseStart_5243997 := by decide
  rcases family_descends (prefixWord ++ tailWord_5243997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5244010 : List Nat := [3, 1, 3, 2, 2, 2, 3, 7]
def baseStart_5244010 : Nat := 118140960795 + 5244010 * 2 ^ 59
def prefixEnd_5244010 : Nat := 4983230072969 + 3 ^ 40 * 5244010 * 2
def baseEnd_5244010 : Nat := 99729543962375297054009

theorem tailTrace_5244010 : CollatzResearch.WordTrace tailWord_5244010 prefixEnd_5244010 99729543962375297054009 := by
  unfold tailWord_5244010
  simp only [CollatzResearch.WordTrace]
  refine ⟨47816189432963712612576371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127509838487903233633536989 47816189432963712612576371)
  ·
    refine ⟨71724284149445568918864557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47816189432963712612576371 71724284149445568918864557)
    ·
      refine ⟨26896606556042088344574209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71724284149445568918864557 26896606556042088344574209)
      ·
        refine ⟨20172454917031566258430657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26896606556042088344574209 20172454917031566258430657)
        ·
          refine ⟨15129341187773674693822993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20172454917031566258430657 15129341187773674693822993)
          ·
            refine ⟨11347005890830256020367245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15129341187773674693822993 11347005890830256020367245)
            ·
              refine ⟨4255127209061346007637717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11347005890830256020367245 4255127209061346007637717)
              ·
                refine ⟨99729543962375297054009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4255127209061346007637717 99729543962375297054009)
                ·
                  rfl

theorem cell23_5244010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 3, 7].length) (baseStart_5244010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5244010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5244010 prefixEnd_5244010 := by exact prefixLift 5244010
  have htrace : WordTrace (prefixWord ++ tailWord_5244010) baseStart_5244010 baseEnd_5244010 := by
    simpa [prefixWord, tailWord_5244010, baseEnd_5244010] using wordTrace_append hprefix tailTrace_5244010
  have hstable : (prefixWord ++ tailWord_5244010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5244010).length < 2 ^ (prefixWord ++ tailWord_5244010).sum := by decide
  have hdescent : baseEnd_5244010 < baseStart_5244010 := by decide
  rcases family_descends (prefixWord ++ tailWord_5244010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5244021 : List Nat := [1, 3, 4, 3, 1, 2, 2, 1, 1, 1, 4]
def baseStart_5244021 : Nat := 118140960795 + 5244021 * 2 ^ 59
def prefixEnd_5244021 : Nat := 4983230072969 + 3 ^ 40 * 5244021 * 2
def baseEnd_5244021 : Nat := 2692703335271332477420693

theorem tailTrace_5244021 : CollatzResearch.WordTrace tailWord_5244021 prefixEnd_5244021 2692703335271332477420693 := by
  unfold tailWord_5244021
  simp only [CollatzResearch.WordTrace]
  refine ⟨191265158934814999328955917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127510105956543332885970611 191265158934814999328955917)
  ·
    refine ⟨71724434600555624748358469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191265158934814999328955917 71724434600555624748358469)
    ·
      refine ⟨13448331487604179640317213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71724434600555624748358469 13448331487604179640317213)
      ·
        refine ⟨5043124307851567365118955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13448331487604179640317213 5043124307851567365118955)
        ·
          refine ⟨7564686461777351047678433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5043124307851567365118955 7564686461777351047678433)
          ·
            refine ⟨5673514846333013285758825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7564686461777351047678433 5673514846333013285758825)
            ·
              refine ⟨4255136134749759964319119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5673514846333013285758825 4255136134749759964319119)
              ·
                refine ⟨6382704202124639946478679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4255136134749759964319119 6382704202124639946478679)
                ·
                  refine ⟨9574056303186959919718019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6382704202124639946478679 9574056303186959919718019)
                  ·
                    refine ⟨14361084454780439879577029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9574056303186959919718019 14361084454780439879577029)
                    ·
                      refine ⟨2692703335271332477420693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14361084454780439879577029 2692703335271332477420693)
                      ·
                        rfl

theorem cell23_5244021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_5244021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5244021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5244021 prefixEnd_5244021 := by exact prefixLift 5244021
  have htrace : WordTrace (prefixWord ++ tailWord_5244021) baseStart_5244021 baseEnd_5244021 := by
    simpa [prefixWord, tailWord_5244021, baseEnd_5244021] using wordTrace_append hprefix tailTrace_5244021
  have hstable : (prefixWord ++ tailWord_5244021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5244021).length < 2 ^ (prefixWord ++ tailWord_5244021).sum := by decide
  have hdescent : baseEnd_5244021 < baseStart_5244021 := by decide
  rcases family_descends (prefixWord ++ tailWord_5244021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5244037 : List Nat := [1, 3, 1, 1, 6, 1, 1, 1, 4, 1, 3]
def baseStart_5244037 : Nat := 118140960795 + 5244037 * 2 ^ 59
def prefixEnd_5244037 : Nat := 4983230072969 + 3 ^ 40 * 5244037 * 2
def baseEnd_5244037 : Nat := 2692711550961804414820619

theorem tailTrace_5244037 : CollatzResearch.WordTrace tailWord_5244037 prefixEnd_5244037 2692711550961804414820619 := by
  unfold tailWord_5244037
  simp only [CollatzResearch.WordTrace]
  refine ⟨191265742502757034061538365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127510495001838022707692243 191265742502757034061538365)
  ·
    refine ⟨71724653438533887773076887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191265742502757034061538365 71724653438533887773076887)
    ·
      refine ⟨107586980157800831659615331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71724653438533887773076887 107586980157800831659615331)
      ·
        refine ⟨161380470236701247489422997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107586980157800831659615331 161380470236701247489422997)
        ·
          refine ⟨7564709542345370976066703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 161380470236701247489422997 7564709542345370976066703)
          ·
            refine ⟨11347064313518056464100055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7564709542345370976066703 11347064313518056464100055)
            ·
              refine ⟨17020596470277084696150083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11347064313518056464100055 17020596470277084696150083)
              ·
                refine ⟨25530894705415627044225125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17020596470277084696150083 25530894705415627044225125)
                ·
                  refine ⟨4787042757265430070792211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25530894705415627044225125 4787042757265430070792211)
                  ·
                    refine ⟨7180564135898145106188317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4787042757265430070792211 7180564135898145106188317)
                    ·
                      refine ⟨2692711550961804414820619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7180564135898145106188317 2692711550961804414820619)
                      ·
                        rfl

theorem cell23_5244037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 4, 1, 3].length) (baseStart_5244037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5244037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5244037 prefixEnd_5244037 := by exact prefixLift 5244037
  have htrace : WordTrace (prefixWord ++ tailWord_5244037) baseStart_5244037 baseEnd_5244037 := by
    simpa [prefixWord, tailWord_5244037, baseEnd_5244037] using wordTrace_append hprefix tailTrace_5244037
  have hstable : (prefixWord ++ tailWord_5244037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5244037).length < 2 ^ (prefixWord ++ tailWord_5244037).sum := by decide
  have hdescent : baseEnd_5244037 < baseStart_5244037 := by decide
  rcases family_descends (prefixWord ++ tailWord_5244037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5244094 : List Nat := [4, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2]
def baseStart_5244094 : Nat := 118140960795 + 5244094 * 2 ^ 59
def prefixEnd_5244094 : Nat := 4983230072969 + 3 ^ 40 * 5244094 * 2
def baseEnd_5244094 : Nat := 2692740819359110691807857

theorem tailTrace_5244094 : CollatzResearch.WordTrace tailWord_5244094 prefixEnd_5244094 2692740819359110691807857 := by
  unfold tailWord_5244094
  simp only [CollatzResearch.WordTrace]
  refine ⟨23908477682943816599545417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127511880975700355197575557 23908477682943816599545417)
  ·
    refine ⟨17931358262207862449659063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23908477682943816599545417 17931358262207862449659063)
    ·
      refine ⟨26897037393311793674488595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17931358262207862449659063 26897037393311793674488595)
      ·
        refine ⟨40345556089967690511732893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26897037393311793674488595 40345556089967690511732893)
        ·
          refine ⟨15129583533737883941899835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40345556089967690511732893 15129583533737883941899835)
          ·
            refine ⟨22694375300606825912849753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15129583533737883941899835 22694375300606825912849753)
            ·
              refine ⟨17020781475455119434637315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22694375300606825912849753 17020781475455119434637315)
              ·
                refine ⟨25531172213182679151955973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17020781475455119434637315 25531172213182679151955973)
                ·
                  refine ⟨4787094789971752340991745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25531172213182679151955973 4787094789971752340991745)
                  ·
                    refine ⟨3590321092478814255743809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4787094789971752340991745 3590321092478814255743809)
                    ·
                      refine ⟨2692740819359110691807857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3590321092478814255743809 2692740819359110691807857)
                      ·
                        rfl

theorem cell23_5244094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2].length) (baseStart_5244094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5244094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5244094 prefixEnd_5244094 := by exact prefixLift 5244094
  have htrace : WordTrace (prefixWord ++ tailWord_5244094) baseStart_5244094 baseEnd_5244094 := by
    simpa [prefixWord, tailWord_5244094, baseEnd_5244094] using wordTrace_append hprefix tailTrace_5244094
  have hstable : (prefixWord ++ tailWord_5244094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5244094).length < 2 ^ (prefixWord ++ tailWord_5244094).sum := by decide
  have hdescent : baseEnd_5244094 < baseStart_5244094 := by decide
  rcases family_descends (prefixWord ++ tailWord_5244094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5244113 : List Nat := [1, 2, 2, 1, 2, 2, 1, 1, 6, 5]
def baseStart_5244113 : Nat := 118140960795 + 5244113 * 2 ^ 59
def prefixEnd_5244113 : Nat := 4983230072969 + 3 ^ 40 * 5244113 * 2
def baseEnd_5244113 : Nat := 897583525163848705823423

theorem tailTrace_5244113 : CollatzResearch.WordTrace tailWord_5244113 prefixEnd_5244113 897583525163848705823423 := by
  unfold tailWord_5244113
  simp only [CollatzResearch.WordTrace]
  refine ⟨191268514450481699041304993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127512342966987799360869995 191268514450481699041304993)
  ·
    refine ⟨143451385837861274280978745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191268514450481699041304993 143451385837861274280978745)
    ·
      refine ⟨107588539378395955710734059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143451385837861274280978745 107588539378395955710734059)
      ·
        refine ⟨161382809067593933566101089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107588539378395955710734059 161382809067593933566101089)
        ·
          refine ⟨121037106800695450174575817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161382809067593933566101089 121037106800695450174575817)
          ·
            refine ⟨90777830100521587630931863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121037106800695450174575817 90777830100521587630931863)
            ·
              refine ⟨136166745150782381446397795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90777830100521587630931863 136166745150782381446397795)
              ·
                refine ⟨204250117726173572169596693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136166745150782381446397795 204250117726173572169596693)
                ·
                  refine ⟨9574224268414386195449845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 204250117726173572169596693 9574224268414386195449845)
                  ·
                    refine ⟨897583525163848705823423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9574224268414386195449845 897583525163848705823423)
                    ·
                      rfl

theorem cell23_5244113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 6, 5].length) (baseStart_5244113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5244113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5244113 prefixEnd_5244113 := by exact prefixLift 5244113
  have htrace : WordTrace (prefixWord ++ tailWord_5244113) baseStart_5244113 baseEnd_5244113 := by
    simpa [prefixWord, tailWord_5244113, baseEnd_5244113] using wordTrace_append hprefix tailTrace_5244113
  have hstable : (prefixWord ++ tailWord_5244113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5244113).length < 2 ^ (prefixWord ++ tailWord_5244113).sum := by decide
  have hdescent : baseEnd_5244113 < baseStart_5244113 := by decide
  rcases family_descends (prefixWord ++ tailWord_5244113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5244150 : List Nat := [5, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4]
def baseStart_5244150 : Nat := 118140960795 + 5244150 * 2 ^ 59
def prefixEnd_5244150 : Nat := 4983230072969 + 3 ^ 40 * 5244150 * 2
def baseEnd_5244150 : Nat := 2692769574275762472707599

theorem tailTrace_5244150 : CollatzResearch.WordTrace tailWord_5244150 prefixEnd_5244150 2692769574275762472707599 := by
  unfold tailWord_5244150
  simp only [CollatzResearch.WordTrace]
  refine ⟨11954366496959228397525119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 127513242634231769573601269 11954366496959228397525119)
  ·
    refine ⟨17931549745438842596287679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11954366496959228397525119 17931549745438842596287679)
    ·
      refine ⟨26897324618158263894431519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17931549745438842596287679 26897324618158263894431519)
      ·
        refine ⟨40345986927237395841647279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26897324618158263894431519 40345986927237395841647279)
        ·
          refine ⟨60518980390856093762470919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40345986927237395841647279 60518980390856093762470919)
          ·
            refine ⟨90778470586284140643706379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60518980390856093762470919 90778470586284140643706379)
            ·
              refine ⟨136167705879426210965559569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90778470586284140643706379 136167705879426210965559569)
              ·
                refine ⟨102125779409569658224169677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136167705879426210965559569 102125779409569658224169677)
                ·
                  refine ⟨38297167278588621834063629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102125779409569658224169677 38297167278588621834063629)
                  ·
                    refine ⟨14361437729470733187773861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38297167278588621834063629 14361437729470733187773861)
                    ·
                      refine ⟨2692769574275762472707599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14361437729470733187773861 2692769574275762472707599)
                      ·
                        rfl

theorem cell23_5244150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_5244150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5244150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5244150 prefixEnd_5244150 := by exact prefixLift 5244150
  have htrace : WordTrace (prefixWord ++ tailWord_5244150) baseStart_5244150 baseEnd_5244150 := by
    simpa [prefixWord, tailWord_5244150, baseEnd_5244150] using wordTrace_append hprefix tailTrace_5244150
  have hstable : (prefixWord ++ tailWord_5244150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5244150).length < 2 ^ (prefixWord ++ tailWord_5244150).sum := by decide
  have hdescent : baseEnd_5244150 < baseStart_5244150 := by decide
  rcases family_descends (prefixWord ++ tailWord_5244150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5244153 : List Nat := [1, 2, 1, 3, 1, 1, 3, 1, 2, 3, 5]
def baseStart_5244153 : Nat := 118140960795 + 5244153 * 2 ^ 59
def prefixEnd_5244153 : Nat := 4983230072969 + 3 ^ 40 * 5244153 * 2
def baseEnd_5244153 : Nat := 2692771114717725960970085

theorem tailTrace_5244153 : CollatzResearch.WordTrace tailWord_5244153 prefixEnd_5244153 2692771114717725960970085 := by
  unfold tailWord_5244153
  simp only [CollatzResearch.WordTrace]
  refine ⟨191269973370336785872761113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127513315580224523915174075 191269973370336785872761113)
  ·
    refine ⟨143452480027752589404570835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191269973370336785872761113 143452480027752589404570835)
    ·
      refine ⟨215178720041628884106856253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143452480027752589404570835 215178720041628884106856253)
      ·
        refine ⟨80692020015610831540071095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 215178720041628884106856253 80692020015610831540071095)
        ·
          refine ⟨121038030023416247310106643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80692020015610831540071095 121038030023416247310106643)
          ·
            refine ⟨181557045035124370965159965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121038030023416247310106643 181557045035124370965159965)
            ·
              refine ⟨68083891888171639111934987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 181557045035124370965159965 68083891888171639111934987)
              ·
                refine ⟨102125837832257458667902481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68083891888171639111934987 102125837832257458667902481)
                ·
                  refine ⟨76594378374193094000926861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102125837832257458667902481 76594378374193094000926861)
                  ·
                    refine ⟨28722891890322410250347573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 76594378374193094000926861 28722891890322410250347573)
                    ·
                      refine ⟨2692771114717725960970085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28722891890322410250347573 2692771114717725960970085)
                      ·
                        rfl

theorem cell23_5244153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_5244153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5244153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5244153 prefixEnd_5244153 := by exact prefixLift 5244153
  have htrace : WordTrace (prefixWord ++ tailWord_5244153) baseStart_5244153 baseEnd_5244153 := by
    simpa [prefixWord, tailWord_5244153, baseEnd_5244153] using wordTrace_append hprefix tailTrace_5244153
  have hstable : (prefixWord ++ tailWord_5244153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5244153).length < 2 ^ (prefixWord ++ tailWord_5244153).sum := by decide
  have hdescent : baseEnd_5244153 < baseStart_5244153 := by decide
  rcases family_descends (prefixWord ++ tailWord_5244153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5244160 : List Nat := [2, 1, 1, 2, 1, 1, 3, 5, 3, 4]
def baseStart_5244160 : Nat := 118140960795 + 5244160 * 2 ^ 59
def prefixEnd_5244160 : Nat := 4983230072969 + 3 ^ 40 * 5244160 * 2
def baseEnd_5244160 : Nat := 897591569694102477860851

theorem tailTrace_5244160 : CollatzResearch.WordTrace tailWord_5244160 prefixEnd_5244160 897591569694102477860851 := by
  unfold tailWord_5244160
  simp only [CollatzResearch.WordTrace]
  refine ⟨95635114340655713034132967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127513485787540950712177289 95635114340655713034132967)
  ·
    refine ⟨143452671510983569551199451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95635114340655713034132967 143452671510983569551199451)
    ·
      refine ⟨215179007266475354326799177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143452671510983569551199451 215179007266475354326799177)
      ·
        refine ⟨161384255449856515745099383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215179007266475354326799177 161384255449856515745099383)
        ·
          refine ⟨242076383174784773617649075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161384255449856515745099383 242076383174784773617649075)
          ·
            refine ⟨363114574762177160426473613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242076383174784773617649075 363114574762177160426473613)
            ·
              refine ⟨136167965535816435159927605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 363114574762177160426473613 136167965535816435159927605)
              ·
                refine ⟨12765746768982790796243213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 136167965535816435159927605 12765746768982790796243213)
                ·
                  refine ⟨4787155038368546548591205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12765746768982790796243213 4787155038368546548591205)
                  ·
                    refine ⟨897591569694102477860851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4787155038368546548591205 897591569694102477860851)
                    ·
                      rfl

theorem cell23_5244160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 5, 3, 4].length) (baseStart_5244160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5244160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5244160 prefixEnd_5244160 := by exact prefixLift 5244160
  have htrace : WordTrace (prefixWord ++ tailWord_5244160) baseStart_5244160 baseEnd_5244160 := by
    simpa [prefixWord, tailWord_5244160, baseEnd_5244160] using wordTrace_append hprefix tailTrace_5244160
  have hstable : (prefixWord ++ tailWord_5244160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5244160).length < 2 ^ (prefixWord ++ tailWord_5244160).sum := by decide
  have hdescent : baseEnd_5244160 < baseStart_5244160 := by decide
  rcases family_descends (prefixWord ++ tailWord_5244160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5244170 : List Nat := [3, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3]
def baseStart_5244170 : Nat := 118140960795 + 5244170 * 2 ^ 59
def prefixEnd_5244170 : Nat := 4983230072969 + 3 ^ 40 * 5244170 * 2
def baseEnd_5244170 : Nat := 2692779843888852394457507

theorem tailTrace_5244170 : CollatzResearch.WordTrace tailWord_5244170 prefixEnd_5244170 2692779843888852394457507 := by
  unfold tailWord_5244170
  simp only [CollatzResearch.WordTrace]
  refine ⟨47817648352818799444032491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127513728940850131850753309 47817648352818799444032491)
  ·
    refine ⟨71726472529228199166048737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47817648352818799444032491 71726472529228199166048737)
    ·
      refine ⟨53794854396921149374536553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71726472529228199166048737 53794854396921149374536553)
      ·
        refine ⟨40346140797690862030902415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53794854396921149374536553 40346140797690862030902415)
        ·
          refine ⟨60519211196536293046353623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40346140797690862030902415 60519211196536293046353623)
          ·
            refine ⟨90778816794804439569530435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60519211196536293046353623 90778816794804439569530435)
            ·
              refine ⟨136168225192206659354295653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90778816794804439569530435 136168225192206659354295653)
              ·
                refine ⟨25531542223538748628930435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 136168225192206659354295653 25531542223538748628930435)
                ·
                  refine ⟨38297313335308122943395653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25531542223538748628930435 38297313335308122943395653)
                  ·
                    refine ⟨7180746250370273051886685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38297313335308122943395653 7180746250370273051886685)
                    ·
                      refine ⟨2692779843888852394457507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7180746250370273051886685 2692779843888852394457507)
                      ·
                        rfl

theorem cell23_5244170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_5244170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5244170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5244170 prefixEnd_5244170 := by exact prefixLift 5244170
  have htrace : WordTrace (prefixWord ++ tailWord_5244170) baseStart_5244170 baseEnd_5244170 := by
    simpa [prefixWord, tailWord_5244170, baseEnd_5244170] using wordTrace_append hprefix tailTrace_5244170
  have hstable : (prefixWord ++ tailWord_5244170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5244170).length < 2 ^ (prefixWord ++ tailWord_5244170).sum := by decide
  have hdescent : baseEnd_5244170 < baseStart_5244170 := by decide
  rcases family_descends (prefixWord ++ tailWord_5244170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5244210 : List Nat := [3, 2, 1, 1, 4, 1, 1, 1, 1, 2, 6]
def baseStart_5244210 : Nat := 118140960795 + 5244210 * 2 ^ 59
def prefixEnd_5244210 : Nat := 4983230072969 + 3 ^ 40 * 5244210 * 2
def baseEnd_5244210 : Nat := 2692800383115032237957323

theorem tailTrace_5244210 : CollatzResearch.WordTrace tailWord_5244210 prefixEnd_5244210 2692800383115032237957323 := by
  unfold tailWord_5244210
  simp only [CollatzResearch.WordTrace]
  refine ⟨47818013082782571151896521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127514701554086856405057389 47818013082782571151896521)
  ·
    refine ⟨35863509812086928363922391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47818013082782571151896521 35863509812086928363922391)
    ·
      refine ⟨53795264718130392545883587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35863509812086928363922391 53795264718130392545883587)
      ·
        refine ⟨80692897077195588818825381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53795264718130392545883587 80692897077195588818825381)
        ·
          refine ⟨15129918201974172903529759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80692897077195588818825381 15129918201974172903529759)
          ·
            refine ⟨22694877302961259355294639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15129918201974172903529759 22694877302961259355294639)
            ·
              refine ⟨34042315954441889032941959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22694877302961259355294639 34042315954441889032941959)
              ·
                refine ⟨51063473931662833549412939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34042315954441889032941959 51063473931662833549412939)
                ·
                  refine ⟨76595210897494250324119409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51063473931662833549412939 76595210897494250324119409)
                  ·
                    refine ⟨57446408173120687743089557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 76595210897494250324119409 57446408173120687743089557)
                    ·
                      refine ⟨2692800383115032237957323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57446408173120687743089557 2692800383115032237957323)
                      ·
                        rfl

theorem cell23_5244210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_5244210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5244210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5244210 prefixEnd_5244210 := by exact prefixLift 5244210
  have htrace : WordTrace (prefixWord ++ tailWord_5244210) baseStart_5244210 baseEnd_5244210 := by
    simpa [prefixWord, tailWord_5244210, baseEnd_5244210] using wordTrace_append hprefix tailTrace_5244210
  have hstable : (prefixWord ++ tailWord_5244210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5244210).length < 2 ^ (prefixWord ++ tailWord_5244210).sum := by decide
  have hdescent : baseEnd_5244210 < baseStart_5244210 := by decide
  rcases family_descends (prefixWord ++ tailWord_5244210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5244244 : List Nat := [2, 4, 1, 1, 2, 1, 2, 3, 2, 3, 2]
def baseStart_5244244 : Nat := 118140960795 + 5244244 * 2 ^ 59
def prefixEnd_5244244 : Nat := 4983230072969 + 3 ^ 40 * 5244244 * 2
def baseEnd_5244244 : Nat := 2692817841457285104932167

theorem tailTrace_5244244 : CollatzResearch.WordTrace tailWord_5244244 prefixEnd_5244244 2692817841457285104932167 := by
  unfold tailWord_5244244
  simp only [CollatzResearch.WordTrace]
  refine ⟨95636646206503554207161893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127515528275338072276215857 95636646206503554207161893)
  ·
    refine ⟨17931871163719416413842855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95636646206503554207161893 17931871163719416413842855)
    ·
      refine ⟨26897806745579124620764283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17931871163719416413842855 26897806745579124620764283)
      ·
        refine ⟨40346710118368686931146425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26897806745579124620764283 40346710118368686931146425)
        ·
          refine ⟨30260032588776515198359819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40346710118368686931146425 30260032588776515198359819)
          ·
            refine ⟨45390048883164772797539729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30260032588776515198359819 45390048883164772797539729)
            ·
              refine ⟨34042536662373579598154797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45390048883164772797539729 34042536662373579598154797)
              ·
                refine ⟨12765951248390092349308049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34042536662373579598154797 12765951248390092349308049)
                ·
                  refine ⟨9574463436292569261981037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12765951248390092349308049 9574463436292569261981037)
                  ·
                    refine ⟨3590423788609713473242889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9574463436292569261981037 3590423788609713473242889)
                    ·
                      refine ⟨2692817841457285104932167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3590423788609713473242889 2692817841457285104932167)
                      ·
                        rfl

theorem cell23_5244244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 3, 2, 3, 2].length) (baseStart_5244244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5244244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5244244 prefixEnd_5244244 := by exact prefixLift 5244244
  have htrace : WordTrace (prefixWord ++ tailWord_5244244) baseStart_5244244 baseEnd_5244244 := by
    simpa [prefixWord, tailWord_5244244, baseEnd_5244244] using wordTrace_append hprefix tailTrace_5244244
  have hstable : (prefixWord ++ tailWord_5244244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5244244).length < 2 ^ (prefixWord ++ tailWord_5244244).sum := by decide
  have hdescent : baseEnd_5244244 < baseStart_5244244 := by decide
  rcases family_descends (prefixWord ++ tailWord_5244244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5244250 : List Nat := [3, 1, 1, 2, 1, 2, 2, 4, 1, 6]
def baseStart_5244250 : Nat := 118140960795 + 5244250 * 2 ^ 59
def prefixEnd_5244250 : Nat := 4983230072969 + 3 ^ 40 * 5244250 * 2
def baseEnd_5244250 : Nat := 897606974113737360485713

theorem tailTrace_5244250 : CollatzResearch.WordTrace tailWord_5244250 prefixEnd_5244250 897606974113737360485713 := by
  unfold tailWord_5244250
  simp only [CollatzResearch.WordTrace]
  refine ⟨47818377812746342859760551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127515674167323580959361469 47818377812746342859760551)
  ·
    refine ⟨71727566719119514289640827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47818377812746342859760551 71727566719119514289640827)
    ·
      refine ⟨107591350078679271434461241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71727566719119514289640827 107591350078679271434461241)
      ·
        refine ⟨80693512559009453575845931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107591350078679271434461241 80693512559009453575845931)
        ·
          refine ⟨121040268838514180363768897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80693512559009453575845931 121040268838514180363768897)
          ·
            refine ⟨90780201628885635272826673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121040268838514180363768897 90780201628885635272826673)
            ·
              refine ⟨68085151221664226454620005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90780201628885635272826673 68085151221664226454620005)
              ·
                refine ⟨12765965854062042460241251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68085151221664226454620005 12765965854062042460241251)
                ·
                  refine ⟨19148948781093063690361877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12765965854062042460241251 19148948781093063690361877)
                  ·
                    refine ⟨897606974113737360485713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19148948781093063690361877 897606974113737360485713)
                    ·
                      rfl

theorem cell23_5244250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 4, 1, 6].length) (baseStart_5244250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5244250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5244250 prefixEnd_5244250 := by exact prefixLift 5244250
  have htrace : WordTrace (prefixWord ++ tailWord_5244250) baseStart_5244250 baseEnd_5244250 := by
    simpa [prefixWord, tailWord_5244250, baseEnd_5244250] using wordTrace_append hprefix tailTrace_5244250
  have hstable : (prefixWord ++ tailWord_5244250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5244250).length < 2 ^ (prefixWord ++ tailWord_5244250).sum := by decide
  have hdescent : baseEnd_5244250 < baseStart_5244250 := by decide
  rcases family_descends (prefixWord ++ tailWord_5244250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5244268 : List Nat := [2, 2, 1, 1, 5, 2, 3, 2, 1, 1, 3]
def baseStart_5244268 : Nat := 118140960795 + 5244268 * 2 ^ 59
def prefixEnd_5244268 : Nat := 4983230072969 + 3 ^ 40 * 5244268 * 2
def baseEnd_5244268 : Nat := 2692830164992993011032057

theorem tailTrace_5244268 : CollatzResearch.WordTrace tailWord_5244268 prefixEnd_5244268 2692830164992993011032057 := by
  unfold tailWord_5244268
  simp only [CollatzResearch.WordTrace]
  refine ⟨95637083882460080256598729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127516111843280107008798305 95637083882460080256598729)
  ·
    refine ⟨71727812911845060192449047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95637083882460080256598729 71727812911845060192449047)
    ·
      refine ⟨107591719367767590288673571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71727812911845060192449047 107591719367767590288673571)
      ·
        refine ⟨161387579051651385433010357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107591719367767590288673571 161387579051651385433010357)
        ·
          refine ⟨15130085536092317384344721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 161387579051651385433010357 15130085536092317384344721)
          ·
            refine ⟨11347564152069238038258541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15130085536092317384344721 11347564152069238038258541)
            ·
              refine ⟨4255336557025964264346953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11347564152069238038258541 4255336557025964264346953)
              ·
                refine ⟨3191502417769473198260215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4255336557025964264346953 3191502417769473198260215)
                ·
                  refine ⟨4787253626654209797390323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3191502417769473198260215 4787253626654209797390323)
                  ·
                    refine ⟨7180880439981314696085485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4787253626654209797390323 7180880439981314696085485)
                    ·
                      refine ⟨2692830164992993011032057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7180880439981314696085485 2692830164992993011032057)
                      ·
                        rfl

theorem cell23_5244268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 3, 2, 1, 1, 3].length) (baseStart_5244268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5244268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5244268 prefixEnd_5244268 := by exact prefixLift 5244268
  have htrace : WordTrace (prefixWord ++ tailWord_5244268) baseStart_5244268 baseEnd_5244268 := by
    simpa [prefixWord, tailWord_5244268, baseEnd_5244268] using wordTrace_append hprefix tailTrace_5244268
  have hstable : (prefixWord ++ tailWord_5244268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5244268).length < 2 ^ (prefixWord ++ tailWord_5244268).sum := by decide
  have hdescent : baseEnd_5244268 < baseStart_5244268 := by decide
  rcases family_descends (prefixWord ++ tailWord_5244268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5244318 : List Nat := [4, 3, 1, 2, 2, 1, 2, 2, 2, 4]
def baseStart_5244318 : Nat := 118140960795 + 5244318 * 2 ^ 59
def prefixEnd_5244318 : Nat := 4983230072969 + 3 ^ 40 * 5244318 * 2
def baseEnd_5244318 : Nat := 897618613008572605135609

theorem tailTrace_5244318 : CollatzResearch.WordTrace tailWord_5244318 prefixEnd_5244318 897618613008572605135609 := by
  unfold tailWord_5244318
  simp only [CollatzResearch.WordTrace]
  refine ⟨23909498926842377381564701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127517327609826012701678405 23909498926842377381564701)
  ·
    refine ⟨8966062097565891518086763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23909498926842377381564701 8966062097565891518086763)
    ·
      refine ⟨13449093146348837277130145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8966062097565891518086763 13449093146348837277130145)
      ·
        refine ⟨10086819859761627957847609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13449093146348837277130145 10086819859761627957847609)
        ·
          refine ⟨7565114894821220968385707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10086819859761627957847609 7565114894821220968385707)
          ·
            refine ⟨11347672342231831452578561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7565114894821220968385707 11347672342231831452578561)
            ·
              refine ⟨8510754256673873589433921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11347672342231831452578561 8510754256673873589433921)
              ·
                refine ⟨6383065692505405192075441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8510754256673873589433921 6383065692505405192075441)
                ·
                  refine ⟨4787299269379053894056581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6383065692505405192075441 4787299269379053894056581)
                  ·
                    refine ⟨897618613008572605135609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4787299269379053894056581 897618613008572605135609)
                    ·
                      rfl

theorem cell23_5244318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_5244318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5244318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5244318 prefixEnd_5244318 := by exact prefixLift 5244318
  have htrace : WordTrace (prefixWord ++ tailWord_5244318) baseStart_5244318 baseEnd_5244318 := by
    simpa [prefixWord, tailWord_5244318, baseEnd_5244318] using wordTrace_append hprefix tailTrace_5244318
  have hstable : (prefixWord ++ tailWord_5244318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5244318).length < 2 ^ (prefixWord ++ tailWord_5244318).sum := by decide
  have hdescent : baseEnd_5244318 < baseStart_5244318 := by decide
  rcases family_descends (prefixWord ++ tailWord_5244318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5244341 : List Nat := [1, 3, 3, 2, 2, 1, 2, 3, 2, 1, 3]
def baseStart_5244341 : Nat := 118140960795 + 5244341 * 2 ^ 59
def prefixEnd_5244341 : Nat := 4983230072969 + 3 ^ 40 * 5244341 * 2
def baseEnd_5244341 : Nat := 2692867649080771225419221

theorem tailTrace_5244341 : CollatzResearch.WordTrace tailWord_5244341 prefixEnd_5244341 2692867649080771225419221 := by
  unfold tailWord_5244341
  simp only [CollatzResearch.WordTrace]
  refine ⟨191276830293655693980604877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127517886862437129320403251 191276830293655693980604877)
  ·
    refine ⟨71728811360120885242726829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191276830293655693980604877 71728811360120885242726829)
    ·
      refine ⟨26898304260045331966022561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71728811360120885242726829 26898304260045331966022561)
      ·
        refine ⟨20173728195033998974516921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26898304260045331966022561 20173728195033998974516921)
        ·
          refine ⟨15130296146275499230887691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20173728195033998974516921 15130296146275499230887691)
          ·
            refine ⟨22695444219413248846331537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15130296146275499230887691 22695444219413248846331537)
            ·
              refine ⟨17021583164559936634748653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22695444219413248846331537 17021583164559936634748653)
              ·
                refine ⟨6383093686709976238030745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17021583164559936634748653 6383093686709976238030745)
                ·
                  refine ⟨4787320265032482178523059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6383093686709976238030745 4787320265032482178523059)
                  ·
                    refine ⟨7180980397548723267784589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4787320265032482178523059 7180980397548723267784589)
                    ·
                      refine ⟨2692867649080771225419221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7180980397548723267784589 2692867649080771225419221)
                      ·
                        rfl

theorem cell23_5244341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_5244341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5244341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5244341 prefixEnd_5244341 := by exact prefixLift 5244341
  have htrace : WordTrace (prefixWord ++ tailWord_5244341) baseStart_5244341 baseEnd_5244341 := by
    simpa [prefixWord, tailWord_5244341, baseEnd_5244341] using wordTrace_append hprefix tailTrace_5244341
  have hstable : (prefixWord ++ tailWord_5244341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5244341).length < 2 ^ (prefixWord ++ tailWord_5244341).sum := by decide
  have hdescent : baseEnd_5244341 < baseStart_5244341 := by decide
  rcases family_descends (prefixWord ++ tailWord_5244341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5244374 : List Nat := [5, 2, 1, 1, 1, 2, 1, 2, 2, 6]
def baseStart_5244374 : Nat := 118140960795 + 5244374 * 2 ^ 59
def prefixEnd_5244374 : Nat := 4983230072969 + 3 ^ 40 * 5244374 * 2
def baseEnd_5244374 : Nat := 897628197980789865435523

theorem tailTrace_5244374 : CollatzResearch.WordTrace tailWord_5244374 prefixEnd_5244374 897628197980789865435523 := by
  unfold tailWord_5244374
  simp only [CollatzResearch.WordTrace]
  refine ⟨11954877118908508788534761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 127518689268357427077704117 11954877118908508788534761)
  ·
    refine ⟨8966157839181381591401071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11954877118908508788534761 8966157839181381591401071)
    ·
      refine ⟨13449236758772072387101607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8966157839181381591401071 13449236758772072387101607)
      ·
        refine ⟨20173855138158108580652411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13449236758772072387101607 20173855138158108580652411)
        ·
          refine ⟨30260782707237162870978617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20173855138158108580652411 30260782707237162870978617)
          ·
            refine ⟨22695587030427872153233963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30260782707237162870978617 22695587030427872153233963)
            ·
              refine ⟨34043380545641808229850945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22695587030427872153233963 34043380545641808229850945)
              ·
                refine ⟨25532535409231356172388209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34043380545641808229850945 25532535409231356172388209)
                ·
                  refine ⟨19149401556923517129291157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25532535409231356172388209 19149401556923517129291157)
                  ·
                    refine ⟨897628197980789865435523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19149401556923517129291157 897628197980789865435523)
                    ·
                      rfl

theorem cell23_5244374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_5244374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5244374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5244374 prefixEnd_5244374 := by exact prefixLift 5244374
  have htrace : WordTrace (prefixWord ++ tailWord_5244374) baseStart_5244374 baseEnd_5244374 := by
    simpa [prefixWord, tailWord_5244374, baseEnd_5244374] using wordTrace_append hprefix tailTrace_5244374
  have hstable : (prefixWord ++ tailWord_5244374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5244374).length < 2 ^ (prefixWord ++ tailWord_5244374).sum := by decide
  have hdescent : baseEnd_5244374 < baseStart_5244374 := by decide
  rcases family_descends (prefixWord ++ tailWord_5244374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5244377 : List Nat := [1, 2, 1, 2, 4, 2, 1, 2, 2, 2, 4]
def baseStart_5244377 : Nat := 118140960795 + 5244377 * 2 ^ 59
def prefixEnd_5244377 : Nat := 4983230072969 + 3 ^ 40 * 5244377 * 2
def baseEnd_5244377 : Nat := 2692886134384333084569055

theorem tailTrace_5244377 : CollatzResearch.WordTrace tailWord_5244377 prefixEnd_5244377 2692886134384333084569055 := by
  unfold tailWord_5244377
  simp only [CollatzResearch.WordTrace]
  refine ⟨191278143321525272128915385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127518762214350181419276923 191278143321525272128915385)
  ·
    refine ⟨143458607491143954096686539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191278143321525272128915385 143458607491143954096686539)
    ·
      refine ⟨215187911236715931145029809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143458607491143954096686539 215187911236715931145029809)
      ·
        refine ⟨161390933427536948358772357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215187911236715931145029809 161390933427536948358772357)
        ·
          refine ⟨30260800017663177817269817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 161390933427536948358772357 30260800017663177817269817)
          ·
            refine ⟨22695600013247383362952363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30260800017663177817269817 22695600013247383362952363)
            ·
              refine ⟨34043400019871075044428545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22695600013247383362952363 34043400019871075044428545)
              ·
                refine ⟨25532550014903306283321409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34043400019871075044428545 25532550014903306283321409)
                ·
                  refine ⟨19149412511177479712491057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25532550014903306283321409 19149412511177479712491057)
                  ·
                    refine ⟨14362059383383109784368293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19149412511177479712491057 14362059383383109784368293)
                    ·
                      refine ⟨2692886134384333084569055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14362059383383109784368293 2692886134384333084569055)
                      ·
                        rfl

theorem cell23_5244377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 2, 2, 4].length) (baseStart_5244377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5244377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5244377 prefixEnd_5244377 := by exact prefixLift 5244377
  have htrace : WordTrace (prefixWord ++ tailWord_5244377) baseStart_5244377 baseEnd_5244377 := by
    simpa [prefixWord, tailWord_5244377, baseEnd_5244377] using wordTrace_append hprefix tailTrace_5244377
  have hstable : (prefixWord ++ tailWord_5244377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5244377).length < 2 ^ (prefixWord ++ tailWord_5244377).sum := by decide
  have hdescent : baseEnd_5244377 < baseStart_5244377 := by decide
  rcases family_descends (prefixWord ++ tailWord_5244377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5244387 : List Nat := [1, 1, 1, 6, 2, 1, 1, 3, 7]
def baseStart_5244387 : Nat := 118140960795 + 5244387 * 2 ^ 59
def prefixEnd_5244387 : Nat := 4983230072969 + 3 ^ 40 * 5244387 * 2
def baseEnd_5244387 : Nat := 299210141021208671716001

theorem tailTrace_5244387 : CollatzResearch.WordTrace tailWord_5244387 prefixEnd_5244387 299210141021208671716001 := by
  unfold tailWord_5244387
  simp only [CollatzResearch.WordTrace]
  refine ⟨191278508051489043836779415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127519005367659362557852943 191278508051489043836779415)
  ·
    refine ⟨286917762077233565755169123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191278508051489043836779415 286917762077233565755169123)
    ·
      refine ⟨430376643115850348632753685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286917762077233565755169123 430376643115850348632753685)
      ·
        refine ⟨20173905146055485092160329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 430376643115850348632753685 20173905146055485092160329)
        ·
          refine ⟨15130428859541613819120247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20173905146055485092160329 15130428859541613819120247)
          ·
            refine ⟨22695643289312420728680371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15130428859541613819120247 22695643289312420728680371)
            ·
              refine ⟨34043464933968631093020557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22695643289312420728680371 34043464933968631093020557)
              ·
                refine ⟨12766299350238236659882709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34043464933968631093020557 12766299350238236659882709)
                ·
                  refine ⟨299210141021208671716001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12766299350238236659882709 299210141021208671716001)
                  ·
                    rfl

theorem cell23_5244387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 3, 7].length) (baseStart_5244387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5244387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5244387 prefixEnd_5244387 := by exact prefixLift 5244387
  have htrace : WordTrace (prefixWord ++ tailWord_5244387) baseStart_5244387 baseEnd_5244387 := by
    simpa [prefixWord, tailWord_5244387, baseEnd_5244387] using wordTrace_append hprefix tailTrace_5244387
  have hstable : (prefixWord ++ tailWord_5244387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5244387).length < 2 ^ (prefixWord ++ tailWord_5244387).sum := by decide
  have hdescent : baseEnd_5244387 < baseStart_5244387 := by decide
  rcases family_descends (prefixWord ++ tailWord_5244387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5244497 : List Nat := [1, 2, 2, 1, 3, 2, 2, 1, 1, 2, 6]
def baseStart_5244497 : Nat := 118140960795 + 5244497 * 2 ^ 59
def prefixEnd_5244497 : Nat := 4983230072969 + 3 ^ 40 * 5244497 * 2
def baseEnd_5244497 : Nat := 2692947752062872615068503

theorem tailTrace_5244497 : CollatzResearch.WordTrace tailWord_5244497 prefixEnd_5244497 2692947752062872615068503 := by
  unfold tailWord_5244497
  simp only [CollatzResearch.WordTrace]
  refine ⟨191282520081090532623283745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127521680054060355082189163 191282520081090532623283745)
  ·
    refine ⟨143461890060817899467462809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191282520081090532623283745 143461890060817899467462809)
    ·
      refine ⟨107596417545613424600597107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143461890060817899467462809 107596417545613424600597107)
      ·
        refine ⟨161394626318420136900895661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107596417545613424600597107 161394626318420136900895661)
        ·
          refine ⟨60522984869407551337835873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161394626318420136900895661 60522984869407551337835873)
          ·
            refine ⟨45392238652055663503376905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60522984869407551337835873 45392238652055663503376905)
            ·
              refine ⟨34044178989041747627532679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45392238652055663503376905 34044178989041747627532679)
              ·
                refine ⟨51066268483562621441299019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34044178989041747627532679 51066268483562621441299019)
                ·
                  refine ⟨76599402725343932161948529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51066268483562621441299019 76599402725343932161948529)
                  ·
                    refine ⟨57449552044007949121461397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 76599402725343932161948529 57449552044007949121461397)
                    ·
                      refine ⟨2692947752062872615068503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57449552044007949121461397 2692947752062872615068503)
                      ·
                        rfl

theorem cell23_5244497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 2, 6].length) (baseStart_5244497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5244497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5244497 prefixEnd_5244497 := by exact prefixLift 5244497
  have htrace : WordTrace (prefixWord ++ tailWord_5244497) baseStart_5244497 baseEnd_5244497 := by
    simpa [prefixWord, tailWord_5244497, baseEnd_5244497] using wordTrace_append hprefix tailTrace_5244497
  have hstable : (prefixWord ++ tailWord_5244497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5244497).length < 2 ^ (prefixWord ++ tailWord_5244497).sum := by decide
  have hdescent : baseEnd_5244497 < baseStart_5244497 := by decide
  rcases family_descends (prefixWord ++ tailWord_5244497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5244498 : List Nat := [3, 2, 2, 1, 2, 3, 1, 4, 1, 4]
def baseStart_5244498 : Nat := 118140960795 + 5244498 * 2 ^ 59
def prefixEnd_5244498 : Nat := 4983230072969 + 3 ^ 40 * 5244498 * 2
def baseEnd_5244498 : Nat := 897649421847842370385333

theorem tailTrace_5244498 : CollatzResearch.WordTrace tailWord_5244498 prefixEnd_5244498 897649421847842370385333 := by
  unfold tailWord_5244498
  simp only [CollatzResearch.WordTrace]
  refine ⟨47820639138521727448517537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127521704369391273196046765 47820639138521727448517537)
  ·
    refine ⟨35865479353891295586388153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47820639138521727448517537 35865479353891295586388153)
    ·
      refine ⟨26899109515418471689791115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35865479353891295586388153 26899109515418471689791115)
      ·
        refine ⟨40348664273127707534686673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26899109515418471689791115 40348664273127707534686673)
        ·
          refine ⟨30261498204845780651015005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40348664273127707534686673 30261498204845780651015005)
          ·
            refine ⟨11348061826817167744130627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30261498204845780651015005 11348061826817167744130627)
            ·
              refine ⟨17022092740225751616195941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11348061826817167744130627 17022092740225751616195941)
              ·
                refine ⟨3191642388792328428036739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17022092740225751616195941 3191642388792328428036739)
                ·
                  refine ⟨4787463583188492642055109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3191642388792328428036739 4787463583188492642055109)
                  ·
                    refine ⟨897649421847842370385333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4787463583188492642055109 897649421847842370385333)
                    ·
                      rfl

theorem cell23_5244498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 4, 1, 4].length) (baseStart_5244498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5244498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5244498 prefixEnd_5244498 := by exact prefixLift 5244498
  have htrace : WordTrace (prefixWord ++ tailWord_5244498) baseStart_5244498 baseEnd_5244498 := by
    simpa [prefixWord, tailWord_5244498, baseEnd_5244498] using wordTrace_append hprefix tailTrace_5244498
  have hstable : (prefixWord ++ tailWord_5244498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5244498).length < 2 ^ (prefixWord ++ tailWord_5244498).sum := by decide
  have hdescent : baseEnd_5244498 < baseStart_5244498 := by decide
  rcases family_descends (prefixWord ++ tailWord_5244498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5244524 : List Nat := [2, 2, 1, 1, 3, 1, 1, 6, 1, 5]
def baseStart_5244524 : Nat := 118140960795 + 5244524 * 2 ^ 59
def prefixEnd_5244524 : Nat := 4983230072969 + 3 ^ 40 * 5244524 * 2
def baseEnd_5244524 : Nat := 897653872013514669810293

theorem tailTrace_5244524 : CollatzResearch.WordTrace tailWord_5244524 prefixEnd_5244524 897653872013514669810293 := by
  unfold tailWord_5244524
  simp only [CollatzResearch.WordTrace]
  refine ⟨95641752425996358117258313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127522336567995144156344417 95641752425996358117258313)
  ·
    refine ⟨71731314319497268587943735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95641752425996358117258313 71731314319497268587943735)
    ·
      refine ⟨107596971479245902881915603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71731314319497268587943735 107596971479245902881915603)
      ·
        refine ⟨161395457218868854322873405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107596971479245902881915603 161395457218868854322873405)
        ·
          refine ⟨60523296457075820371077527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161395457218868854322873405 60523296457075820371077527)
          ·
            refine ⟨90784944685613730556616291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60523296457075820371077527 90784944685613730556616291)
            ·
              refine ⟨136177417028420595834924437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90784944685613730556616291 136177417028420595834924437)
              ·
                refine ⟨6383316423207215429762083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 136177417028420595834924437 6383316423207215429762083)
                ·
                  refine ⟨9574974634810823144643125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6383316423207215429762083 9574974634810823144643125)
                  ·
                    refine ⟨897653872013514669810293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9574974634810823144643125 897653872013514669810293)
                    ·
                      rfl

theorem cell23_5244524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 5].length) (baseStart_5244524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5244524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5244524 prefixEnd_5244524 := by exact prefixLift 5244524
  have htrace : WordTrace (prefixWord ++ tailWord_5244524) baseStart_5244524 baseEnd_5244524 := by
    simpa [prefixWord, tailWord_5244524, baseEnd_5244524] using wordTrace_append hprefix tailTrace_5244524
  have hstable : (prefixWord ++ tailWord_5244524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5244524).length < 2 ^ (prefixWord ++ tailWord_5244524).sum := by decide
  have hdescent : baseEnd_5244524 < baseStart_5244524 := by decide
  rcases family_descends (prefixWord ++ tailWord_5244524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5244525 : List Nat := [1, 5, 1, 1, 5, 1, 1, 1, 2, 2, 3]
def baseStart_5244525 : Nat := 118140960795 + 5244525 * 2 ^ 59
def prefixEnd_5244525 : Nat := 4983230072969 + 3 ^ 40 * 5244525 * 2
def baseEnd_5244525 : Nat := 2692962129521198505518375

theorem tailTrace_5244525 : CollatzResearch.WordTrace tailWord_5244525 prefixEnd_5244525 2692962129521198505518375 := by
  unfold tailWord_5244525
  simp only [CollatzResearch.WordTrace]
  refine ⟨191283541324989093405303029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127522360883326062270202019 191283541324989093405303029)
  ·
    refine ⟨17932831999217727506747159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 191283541324989093405303029 17932831999217727506747159)
    ·
      refine ⟨26899247998826591260120739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17932831999217727506747159 26899247998826591260120739)
      ·
        refine ⟨40348871998239886890181109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26899247998826591260120739 40348871998239886890181109)
        ·
          refine ⟨3782706749834989395954479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40348871998239886890181109 3782706749834989395954479)
          ·
            refine ⟨5674060124752484093931719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3782706749834989395954479 5674060124752484093931719)
            ·
              refine ⟨8511090187128726140897579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5674060124752484093931719 8511090187128726140897579)
              ·
                refine ⟨12766635280693089211346369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8511090187128726140897579 12766635280693089211346369)
                ·
                  refine ⟨9574976460519816908509777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12766635280693089211346369 9574976460519816908509777)
                  ·
                    refine ⟨7181232345389862681382333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9574976460519816908509777 7181232345389862681382333)
                    ·
                      refine ⟨2692962129521198505518375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7181232345389862681382333 2692962129521198505518375)
                      ·
                        rfl

theorem cell23_5244525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 1, 2, 2, 3].length) (baseStart_5244525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5244525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5244525 prefixEnd_5244525 := by exact prefixLift 5244525
  have htrace : WordTrace (prefixWord ++ tailWord_5244525) baseStart_5244525 baseEnd_5244525 := by
    simpa [prefixWord, tailWord_5244525, baseEnd_5244525] using wordTrace_append hprefix tailTrace_5244525
  have hstable : (prefixWord ++ tailWord_5244525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5244525).length < 2 ^ (prefixWord ++ tailWord_5244525).sum := by decide
  have hdescent : baseEnd_5244525 < baseStart_5244525 := by decide
  rcases family_descends (prefixWord ++ tailWord_5244525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5244541 : List Nat := [1, 4, 1, 1, 4, 2, 1, 3, 1, 5]
def baseStart_5244541 : Nat := 118140960795 + 5244541 * 2 ^ 59
def prefixEnd_5244541 : Nat := 4983230072969 + 3 ^ 40 * 5244541 * 2
def baseEnd_5244541 : Nat := 897656781737223480972767

theorem tailTrace_5244541 : CollatzResearch.WordTrace tailWord_5244541 prefixEnd_5244541 897656781737223480972767 := by
  unfold tailWord_5244541
  simp only [CollatzResearch.WordTrace]
  refine ⟨191284124892931128137885477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127522749928620752091923651 191284124892931128137885477)
  ·
    refine ⟨35865773417424586525853527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 191284124892931128137885477 35865773417424586525853527)
    ·
      refine ⟨53798660126136879788780291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35865773417424586525853527 53798660126136879788780291)
      ·
        refine ⟨80697990189205319683170437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53798660126136879788780291 80697990189205319683170437)
        ·
          refine ⟨15130873160475997440594457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80697990189205319683170437 15130873160475997440594457)
          ·
            refine ⟨11348154870356998080445843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15130873160475997440594457 11348154870356998080445843)
            ·
              refine ⟨17022232305535497120668765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11348154870356998080445843 17022232305535497120668765)
              ·
                refine ⟨6383337114575811420250787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17022232305535497120668765 6383337114575811420250787)
                ·
                  refine ⟨9575005671863717130376181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6383337114575811420250787 9575005671863717130376181)
                  ·
                    refine ⟨897656781737223480972767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9575005671863717130376181 897656781737223480972767)
                    ·
                      rfl

theorem cell23_5244541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 3, 1, 5].length) (baseStart_5244541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5244541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5244541 prefixEnd_5244541 := by exact prefixLift 5244541
  have htrace : WordTrace (prefixWord ++ tailWord_5244541) baseStart_5244541 baseEnd_5244541 := by
    simpa [prefixWord, tailWord_5244541, baseEnd_5244541] using wordTrace_append hprefix tailTrace_5244541
  have hstable : (prefixWord ++ tailWord_5244541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5244541).length < 2 ^ (prefixWord ++ tailWord_5244541).sum := by decide
  have hdescent : baseEnd_5244541 < baseStart_5244541 := by decide
  rcases family_descends (prefixWord ++ tailWord_5244541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5244581 : List Nat := [1, 3, 1, 2, 1, 2, 3, 4, 1, 2, 3]
def baseStart_5244581 : Nat := 118140960795 + 5244581 * 2 ^ 59
def prefixEnd_5244581 : Nat := 4983230072969 + 3 ^ 40 * 5244581 * 2
def baseEnd_5244581 : Nat := 2692990884437850286418117

theorem tailTrace_5244581 : CollatzResearch.WordTrace tailWord_5244581 prefixEnd_5244581 2692990884437850286418117 := by
  unfold tailWord_5244581
  simp only [CollatzResearch.WordTrace]
  refine ⟨191285583812786214969341597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127523722541857476646227731 191285583812786214969341597)
  ·
    refine ⟨71732093929794830613503099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191285583812786214969341597 71732093929794830613503099)
    ·
      refine ⟨107598140894692245920254649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71732093929794830613503099 107598140894692245920254649)
      ·
        refine ⟨80698605671019184440190987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107598140894692245920254649 80698605671019184440190987)
        ·
          refine ⟨121047908506528776660286481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80698605671019184440190987 121047908506528776660286481)
          ·
            refine ⟨90785931379896582495214861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121047908506528776660286481 90785931379896582495214861)
            ·
              refine ⟨34044724267461218435705573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90785931379896582495214861 34044724267461218435705573)
              ·
                refine ⟨6383385800148978456694795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34044724267461218435705573 6383385800148978456694795)
                ·
                  refine ⟨9575078700223467685042193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6383385800148978456694795 9575078700223467685042193)
                  ·
                    refine ⟨7181309025167600763781645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9575078700223467685042193 7181309025167600763781645)
                    ·
                      refine ⟨2692990884437850286418117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7181309025167600763781645 2692990884437850286418117)
                      ·
                        rfl

theorem cell23_5244581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 4, 1, 2, 3].length) (baseStart_5244581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5244581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5244581 prefixEnd_5244581 := by exact prefixLift 5244581
  have htrace : WordTrace (prefixWord ++ tailWord_5244581) baseStart_5244581 baseEnd_5244581 := by
    simpa [prefixWord, tailWord_5244581, baseEnd_5244581] using wordTrace_append hprefix tailTrace_5244581
  have hstable : (prefixWord ++ tailWord_5244581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5244581).length < 2 ^ (prefixWord ++ tailWord_5244581).sum := by decide
  have hdescent : baseEnd_5244581 < baseStart_5244581 := by decide
  rcases family_descends (prefixWord ++ tailWord_5244581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5244598 : List Nat := [5, 1, 3, 1, 1, 1, 1, 3, 1, 1, 5]
def baseStart_5244598 : Nat := 118140960795 + 5244598 * 2 ^ 59
def prefixEnd_5244598 : Nat := 4983230072969 + 3 ^ 40 * 5244598 * 2
def baseEnd_5244598 : Nat := 2692999613608976719905539

theorem tailTrace_5244598 : CollatzResearch.WordTrace tailWord_5244598 prefixEnd_5244598 2692999613608976719905539 := by
  unfold tailWord_5244598
  simp only [CollatzResearch.WordTrace]
  refine ⟨11955387740857789179544403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 127524135902483084581806965 11955387740857789179544403)
  ·
    refine ⟨17933081611286683769316605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11955387740857789179544403 17933081611286683769316605)
    ·
      refine ⟨6724905604232506413493727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17933081611286683769316605 6724905604232506413493727)
      ·
        refine ⟨10087358406348759620240591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6724905604232506413493727 10087358406348759620240591)
        ·
          refine ⟨15131037609523139430360887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10087358406348759620240591 15131037609523139430360887)
          ·
            refine ⟨22696556414284709145541331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15131037609523139430360887 22696556414284709145541331)
            ·
              refine ⟨34044834621427063718311997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22696556414284709145541331 34044834621427063718311997)
              ·
                refine ⟨12766812983035148894366999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34044834621427063718311997 12766812983035148894366999)
                ·
                  refine ⟨19150219474552723341550499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12766812983035148894366999 19150219474552723341550499)
                  ·
                    refine ⟨28725329211829085012325749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19150219474552723341550499 28725329211829085012325749)
                    ·
                      refine ⟨2692999613608976719905539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28725329211829085012325749 2692999613608976719905539)
                      ·
                        rfl

theorem cell23_5244598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_5244598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5244598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5244598 prefixEnd_5244598 := by exact prefixLift 5244598
  have htrace : WordTrace (prefixWord ++ tailWord_5244598) baseStart_5244598 baseEnd_5244598 := by
    simpa [prefixWord, tailWord_5244598, baseEnd_5244598] using wordTrace_append hprefix tailTrace_5244598
  have hstable : (prefixWord ++ tailWord_5244598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5244598).length < 2 ^ (prefixWord ++ tailWord_5244598).sum := by decide
  have hdescent : baseEnd_5244598 < baseStart_5244598 := by decide
  rcases family_descends (prefixWord ++ tailWord_5244598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5244651 : List Nat := [1, 1, 1, 1, 2, 4, 3, 1, 3, 4, 2]
def baseStart_5244651 : Nat := 118140960795 + 5244651 * 2 ^ 59
def prefixEnd_5244651 : Nat := 4983230072969 + 3 ^ 40 * 5244651 * 2
def baseEnd_5244651 : Nat := 2693026828083665012542795

theorem tailTrace_5244651 : CollatzResearch.WordTrace tailWord_5244651 prefixEnd_5244651 2693026828083665012542795 := by
  unfold tailWord_5244651
  simp only [CollatzResearch.WordTrace]
  refine ⟨191288136922532616924389807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127525424615021744616259871 191288136922532616924389807)
  ·
    refine ⟨286932205383798925386584711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191288136922532616924389807 286932205383798925386584711)
    ·
      refine ⟨430398308075698388079877067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286932205383798925386584711 430398308075698388079877067)
      ·
        refine ⟨645597462113547582119815601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 430398308075698388079877067 645597462113547582119815601)
        ·
          refine ⟨484198096585160686589861701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 645597462113547582119815601 484198096585160686589861701)
          ·
            refine ⟨90787143109717628735599069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 484198096585160686589861701 90787143109717628735599069)
            ·
              refine ⟨34045178666144110775849651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90787143109717628735599069 34045178666144110775849651)
              ·
                refine ⟨51067767999216166163774477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34045178666144110775849651 51067767999216166163774477)
                ·
                  refine ⟨19150412999706062311415429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51067767999216166163774477 19150412999706062311415429)
                  ·
                    refine ⟨3590702437444886683390393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19150412999706062311415429 3590702437444886683390393)
                    ·
                      refine ⟨2693026828083665012542795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3590702437444886683390393 2693026828083665012542795)
                      ·
                        rfl

theorem cell23_5244651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 3, 4, 2].length) (baseStart_5244651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5244651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5244651 prefixEnd_5244651 := by exact prefixLift 5244651
  have htrace : WordTrace (prefixWord ++ tailWord_5244651) baseStart_5244651 baseEnd_5244651 := by
    simpa [prefixWord, tailWord_5244651, baseEnd_5244651] using wordTrace_append hprefix tailTrace_5244651
  have hstable : (prefixWord ++ tailWord_5244651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5244651).length < 2 ^ (prefixWord ++ tailWord_5244651).sum := by decide
  have hdescent : baseEnd_5244651 < baseStart_5244651 := by decide
  rcases family_descends (prefixWord ++ tailWord_5244651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5244655 : List Nat := [1, 1, 2, 1, 5, 1, 5, 1, 1, 3, 2]
def baseStart_5244655 : Nat := 118140960795 + 5244655 * 2 ^ 59
def prefixEnd_5244655 : Nat := 4983230072969 + 3 ^ 40 * 5244655 * 2
def baseEnd_5244655 : Nat := 2693028882006282996892777

theorem tailTrace_5244655 : CollatzResearch.WordTrace tailWord_5244655 prefixEnd_5244655 2693028882006282996892777 := by
  unfold tailWord_5244655
  simp only [CollatzResearch.WordTrace]
  refine ⟨191288282814518125607535419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127525521876345417071690279 191288282814518125607535419)
  ·
    refine ⟨286932424221777188411303129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191288282814518125607535419 286932424221777188411303129)
    ·
      refine ⟨215199318166332891308477347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286932424221777188411303129 215199318166332891308477347)
      ·
        refine ⟨322798977249499336962716021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215199318166332891308477347 322798977249499336962716021)
        ·
          refine ⟨30262404117140562840254627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 322798977249499336962716021 30262404117140562840254627)
          ·
            refine ⟨45393606175710844260381941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30262404117140562840254627 45393606175710844260381941)
            ·
              refine ⟨4255650578972891649410807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45393606175710844260381941 4255650578972891649410807)
              ·
                refine ⟨6383475868459337474116211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4255650578972891649410807 6383475868459337474116211)
                ·
                  refine ⟨9575213802689006211174317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6383475868459337474116211 9575213802689006211174317)
                  ·
                    refine ⟨3590705176008377329190369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9575213802689006211174317 3590705176008377329190369)
                    ·
                      refine ⟨2693028882006282996892777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3590705176008377329190369 2693028882006282996892777)
                      ·
                        rfl

theorem cell23_5244655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 5, 1, 1, 3, 2].length) (baseStart_5244655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5244655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5244655 prefixEnd_5244655 := by exact prefixLift 5244655
  have htrace : WordTrace (prefixWord ++ tailWord_5244655) baseStart_5244655 baseEnd_5244655 := by
    simpa [prefixWord, tailWord_5244655, baseEnd_5244655] using wordTrace_append hprefix tailTrace_5244655
  have hstable : (prefixWord ++ tailWord_5244655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5244655).length < 2 ^ (prefixWord ++ tailWord_5244655).sum := by decide
  have hdescent : baseEnd_5244655 < baseStart_5244655 := by decide
  rcases family_descends (prefixWord ++ tailWord_5244655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5244708 : List Nat := [2, 3, 1, 3, 2, 1, 1, 5, 5]
def baseStart_5244708 : Nat := 118140960795 + 5244708 * 2 ^ 59
def prefixEnd_5244708 : Nat := 4983230072969 + 3 ^ 40 * 5244708 * 2
def baseEnd_5244708 : Nat := 299228455164552365503337

theorem tailTrace_5244708 : CollatzResearch.WordTrace tailWord_5244708 prefixEnd_5244708 299228455164552365503337 := by
  unfold tailWord_5244708
  simp only [CollatzResearch.WordTrace]
  refine ⟨95645107941663057829607389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127526810588884077106143185 95645107941663057829607389)
  ·
    refine ⟨35866915478123646686102771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95645107941663057829607389 35866915478123646686102771)
    ·
      refine ⟨53800373217185470029154157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35866915478123646686102771 53800373217185470029154157)
      ·
        refine ⟨20175139956444551260932809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53800373217185470029154157 20175139956444551260932809)
        ·
          refine ⟨15131354967333413445699607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20175139956444551260932809 15131354967333413445699607)
          ·
            refine ⟨22697032451000120168549411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15131354967333413445699607 22697032451000120168549411)
            ·
              refine ⟨34045548676500180252824117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22697032451000120168549411 34045548676500180252824117)
              ·
                refine ⟨3191770188421891898702261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34045548676500180252824117 3191770188421891898702261)
                ·
                  refine ⟨299228455164552365503337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3191770188421891898702261 299228455164552365503337)
                  ·
                    rfl

theorem cell23_5244708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 5, 5].length) (baseStart_5244708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5244708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5244708 prefixEnd_5244708 := by exact prefixLift 5244708
  have htrace : WordTrace (prefixWord ++ tailWord_5244708) baseStart_5244708 baseEnd_5244708 := by
    simpa [prefixWord, tailWord_5244708, baseEnd_5244708] using wordTrace_append hprefix tailTrace_5244708
  have hstable : (prefixWord ++ tailWord_5244708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5244708).length < 2 ^ (prefixWord ++ tailWord_5244708).sum := by decide
  have hdescent : baseEnd_5244708 < baseStart_5244708 := by decide
  rcases family_descends (prefixWord ++ tailWord_5244708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5244761 : List Nat := [1, 2, 1, 2, 2, 3, 1, 3, 1, 4, 3]
def baseStart_5244761 : Nat := 118140960795 + 5244761 * 2 ^ 59
def prefixEnd_5244761 : Nat := 4983230072969 + 3 ^ 40 * 5244761 * 2
def baseEnd_5244761 : Nat := 2693083310955659582167289

theorem tailTrace_5244761 : CollatzResearch.WordTrace tailWord_5244761 prefixEnd_5244761 2693083310955659582167289 := by
  unfold tailWord_5244761
  simp only [CollatzResearch.WordTrace]
  refine ⟨191292148952134105710894137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127528099301422737140596091 191292148952134105710894137)
  ·
    refine ⟨143469111714100579283170603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191292148952134105710894137 143469111714100579283170603)
    ·
      refine ⟨215203667571150868924755905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143469111714100579283170603 215203667571150868924755905)
      ·
        refine ⟨161402750678363151693566929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215203667571150868924755905 161402750678363151693566929)
        ·
          refine ⟨121052063008772363770175197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161402750678363151693566929 121052063008772363770175197)
          ·
            refine ⟨45394523628289636413815699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121052063008772363770175197 45394523628289636413815699)
            ·
              refine ⟨68091785442434454620723549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45394523628289636413815699 68091785442434454620723549)
              ·
                refine ⟨25534419540912920482771331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68091785442434454620723549 25534419540912920482771331)
                ·
                  refine ⟨38301629311369380724156997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25534419540912920482771331 38301629311369380724156997)
                  ·
                    refine ⟨7181555495881758885779437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38301629311369380724156997 7181555495881758885779437)
                    ·
                      refine ⟨2693083310955659582167289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7181555495881758885779437 2693083310955659582167289)
                      ·
                        rfl

theorem cell23_5244761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 4, 3].length) (baseStart_5244761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5244761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5244761 prefixEnd_5244761 := by exact prefixLift 5244761
  have htrace : WordTrace (prefixWord ++ tailWord_5244761) baseStart_5244761 baseEnd_5244761 := by
    simpa [prefixWord, tailWord_5244761, baseEnd_5244761] using wordTrace_append hprefix tailTrace_5244761
  have hstable : (prefixWord ++ tailWord_5244761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5244761).length < 2 ^ (prefixWord ++ tailWord_5244761).sum := by decide
  have hdescent : baseEnd_5244761 < baseStart_5244761 := by decide
  rcases family_descends (prefixWord ++ tailWord_5244761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5244781 : List Nat := [1, 5, 1, 1, 1, 1, 4, 1, 8]
def baseStart_5244781 : Nat := 118140960795 + 5244781 * 2 ^ 59
def prefixEnd_5244781 : Nat := 4983230072969 + 3 ^ 40 * 5244781 * 2
def baseEnd_5244781 : Nat := 299232620063194389324133

theorem tailTrace_5244781 : CollatzResearch.WordTrace tailWord_5244781 prefixEnd_5244781 299232620063194389324133 := by
  unfold tailWord_5244781
  simp only [CollatzResearch.WordTrace]
  refine ⟨191292878412061649126622197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127528585608041099417748131 191292878412061649126622197)
  ·
    refine ⟨17933707351130779605620831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 191292878412061649126622197 17933707351130779605620831)
    ·
      refine ⟨26900561026696169408431247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17933707351130779605620831 26900561026696169408431247)
      ·
        refine ⟨40350841540044254112646871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26900561026696169408431247 40350841540044254112646871)
        ·
          refine ⟨60526262310066381168970307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40350841540044254112646871 60526262310066381168970307)
          ·
            refine ⟨90789393465099571753455461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60526262310066381168970307 90789393465099571753455461)
            ·
              refine ⟨17023011274706169703772899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90789393465099571753455461 17023011274706169703772899)
              ·
                refine ⟨25534516912059254555659349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17023011274706169703772899 25534516912059254555659349)
                ·
                  refine ⟨299232620063194389324133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25534516912059254555659349 299232620063194389324133)
                  ·
                    rfl

theorem cell23_5244781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 8].length) (baseStart_5244781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5244781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5244781 prefixEnd_5244781 := by exact prefixLift 5244781
  have htrace : WordTrace (prefixWord ++ tailWord_5244781) baseStart_5244781 baseEnd_5244781 := by
    simpa [prefixWord, tailWord_5244781, baseEnd_5244781] using wordTrace_append hprefix tailTrace_5244781
  have hstable : (prefixWord ++ tailWord_5244781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5244781).length < 2 ^ (prefixWord ++ tailWord_5244781).sum := by decide
  have hdescent : baseEnd_5244781 < baseStart_5244781 := by decide
  rcases family_descends (prefixWord ++ tailWord_5244781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5244851 : List Nat := [1, 1, 1, 2, 3, 1, 4, 1, 3, 1, 5]
def baseStart_5244851 : Nat := 118140960795 + 5244851 * 2 ^ 59
def prefixEnd_5244851 : Nat := 4983230072969 + 3 ^ 40 * 5244851 * 2
def baseEnd_5244851 : Nat := 2693129524214564230041875

theorem tailTrace_5244851 : CollatzResearch.WordTrace tailWord_5244851 prefixEnd_5244851 2693129524214564230041875 := by
  unfold tailWord_5244851
  simp only [CollatzResearch.WordTrace]
  refine ⟨191295431521808051081670407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127530287681205367387780271 191295431521808051081670407)
  ·
    refine ⟨286943147282712076622505611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191295431521808051081670407 286943147282712076622505611)
    ·
      refine ⟨430414720924068114933758417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286943147282712076622505611 430414720924068114933758417)
      ·
        refine ⟨322811040693051086200318813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 430414720924068114933758417 322811040693051086200318813)
        ·
          refine ⟨121054140259894157325119555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 322811040693051086200318813 121054140259894157325119555)
          ·
            refine ⟨181581210389841235987679333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121054140259894157325119555 181581210389841235987679333)
            ·
              refine ⟨34046476948095231747689875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 181581210389841235987679333 34046476948095231747689875)
              ·
                refine ⟨51069715422142847621534813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34046476948095231747689875 51069715422142847621534813)
                ·
                  refine ⟨19151143283303567858075555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51069715422142847621534813 19151143283303567858075555)
                  ·
                    refine ⟨28726714924955351787113333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19151143283303567858075555 28726714924955351787113333)
                    ·
                      refine ⟨2693129524214564230041875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28726714924955351787113333 2693129524214564230041875)
                      ·
                        rfl

theorem cell23_5244851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 3, 1, 5].length) (baseStart_5244851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5244851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5244851 prefixEnd_5244851 := by exact prefixLift 5244851
  have htrace : WordTrace (prefixWord ++ tailWord_5244851) baseStart_5244851 baseEnd_5244851 := by
    simpa [prefixWord, tailWord_5244851, baseEnd_5244851] using wordTrace_append hprefix tailTrace_5244851
  have hstable : (prefixWord ++ tailWord_5244851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5244851).length < 2 ^ (prefixWord ++ tailWord_5244851).sum := by decide
  have hdescent : baseEnd_5244851 < baseStart_5244851 := by decide
  rcases family_descends (prefixWord ++ tailWord_5244851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5244878 : List Nat := [4, 1, 1, 1, 2, 2, 1, 4, 1, 2, 4]
def baseStart_5244878 : Nat := 118140960795 + 5244878 * 2 ^ 59
def prefixEnd_5244878 : Nat := 4983230072969 + 3 ^ 40 * 5244878 * 2
def baseEnd_5244878 : Nat := 2693143388192235624404251

theorem tailTrace_5244878 : CollatzResearch.WordTrace tailWord_5244878 prefixEnd_5244878 2693143388192235624404251 := by
  unfold tailWord_5244878
  simp only [CollatzResearch.WordTrace]
  refine ⟨23912052036588779336612911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127530944195140156461935525 23912052036588779336612911)
  ·
    refine ⟨35868078054883169004919367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23912052036588779336612911 35868078054883169004919367)
    ·
      refine ⟨53802117082324753507379051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35868078054883169004919367 53802117082324753507379051)
      ·
        refine ⟨80703175623487130261068577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53802117082324753507379051 80703175623487130261068577)
        ·
          refine ⟨60527381717615347695801433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80703175623487130261068577 60527381717615347695801433)
          ·
            refine ⟨45395536288211510771851075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60527381717615347695801433 45395536288211510771851075)
            ·
              refine ⟨68093304432317266157776613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45395536288211510771851075 68093304432317266157776613)
              ·
                refine ⟨12767494581059487404583115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68093304432317266157776613 12767494581059487404583115)
                ·
                  refine ⟨19151241871589231106874673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12767494581059487404583115 19151241871589231106874673)
                  ·
                    refine ⟨14363431403691923330156005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19151241871589231106874673 14363431403691923330156005)
                    ·
                      refine ⟨2693143388192235624404251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14363431403691923330156005 2693143388192235624404251)
                      ·
                        rfl

theorem cell23_5244878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 4, 1, 2, 4].length) (baseStart_5244878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5244878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5244878 prefixEnd_5244878 := by exact prefixLift 5244878
  have htrace : WordTrace (prefixWord ++ tailWord_5244878) baseStart_5244878 baseEnd_5244878 := by
    simpa [prefixWord, tailWord_5244878, baseEnd_5244878] using wordTrace_append hprefix tailTrace_5244878
  have hstable : (prefixWord ++ tailWord_5244878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5244878).length < 2 ^ (prefixWord ++ tailWord_5244878).sum := by decide
  have hdescent : baseEnd_5244878 < baseStart_5244878 := by decide
  rcases family_descends (prefixWord ++ tailWord_5244878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5244882 : List Nat := [3, 2, 2, 3, 2, 1, 1, 3, 1, 1, 4]
def baseStart_5244882 : Nat := 118140960795 + 5244882 * 2 ^ 59
def prefixEnd_5244882 : Nat := 4983230072969 + 3 ^ 40 * 5244882 * 2
def baseEnd_5244882 : Nat := 2693145442114853608754233

theorem tailTrace_5244882 : CollatzResearch.WordTrace tailWord_5244882 prefixEnd_5244882 2693145442114853608754233 := by
  unfold tailWord_5244882
  simp only [CollatzResearch.WordTrace]
  refine ⟨47824140546173935844012225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127531041456463828917365933 47824140546173935844012225)
  ·
    refine ⟨35868105409630451883009169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47824140546173935844012225 35868105409630451883009169)
    ·
      refine ⟨26901079057222838912256877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35868105409630451883009169 26901079057222838912256877)
      ·
        refine ⟨10087904646458564592096329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26901079057222838912256877 10087904646458564592096329)
        ·
          refine ⟨7565928484843923444072247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10087904646458564592096329 7565928484843923444072247)
          ·
            refine ⟨11348892727265885166108371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7565928484843923444072247 11348892727265885166108371)
            ·
              refine ⟨17023339090898827749162557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11348892727265885166108371 17023339090898827749162557)
              ·
                refine ⟨6383752159087060405935959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17023339090898827749162557 6383752159087060405935959)
                ·
                  refine ⟨9575628238630590608903939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6383752159087060405935959 9575628238630590608903939)
                  ·
                    refine ⟨14363442357945885913355909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9575628238630590608903939 14363442357945885913355909)
                    ·
                      refine ⟨2693145442114853608754233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14363442357945885913355909 2693145442114853608754233)
                      ·
                        rfl

theorem cell23_5244882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_5244882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5244882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5244882 prefixEnd_5244882 := by exact prefixLift 5244882
  have htrace : WordTrace (prefixWord ++ tailWord_5244882) baseStart_5244882 baseEnd_5244882 := by
    simpa [prefixWord, tailWord_5244882, baseEnd_5244882] using wordTrace_append hprefix tailTrace_5244882
  have hstable : (prefixWord ++ tailWord_5244882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5244882).length < 2 ^ (prefixWord ++ tailWord_5244882).sum := by decide
  have hdescent : baseEnd_5244882 < baseStart_5244882 := by decide
  rcases family_descends (prefixWord ++ tailWord_5244882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5244899 : List Nat := [1, 1, 1, 6, 1, 2, 2, 4, 1, 2, 2]
def baseStart_5244899 : Nat := 118140960795 + 5244899 * 2 ^ 59
def prefixEnd_5244899 : Nat := 4983230072969 + 3 ^ 40 * 5244899 * 2
def baseEnd_5244899 : Nat := 2693154171285980042241655

theorem tailTrace_5244899 : CollatzResearch.WordTrace tailWord_5244899 prefixEnd_5244899 2693154171285980042241655 := by
  unfold tailWord_5244899
  simp only [CollatzResearch.WordTrace]
  refine ⟨191297182225634155279417751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127531454817089436852945167 191297182225634155279417751)
  ·
    refine ⟨286945773338451232919126627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191297182225634155279417751 286945773338451232919126627)
    ·
      refine ⟨430418660007676849378689941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286945773338451232919126627 430418660007676849378689941)
      ·
        refine ⟨20175874687859852314626091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 430418660007676849378689941 20175874687859852314626091)
        ·
          refine ⟨30263812031789778471939137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20175874687859852314626091 30263812031789778471939137)
          ·
            refine ⟨22697859023842333853954353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30263812031789778471939137 22697859023842333853954353)
            ·
              refine ⟨17023394267881750390465765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22697859023842333853954353 17023394267881750390465765)
              ·
                refine ⟨3191886425227828198212331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17023394267881750390465765 3191886425227828198212331)
                ·
                  refine ⟨4787829637841742297318497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3191886425227828198212331 4787829637841742297318497)
                  ·
                    refine ⟨3590872228381306722988873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4787829637841742297318497 3590872228381306722988873)
                    ·
                      refine ⟨2693154171285980042241655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3590872228381306722988873 2693154171285980042241655)
                      ·
                        rfl

theorem cell23_5244899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 4, 1, 2, 2].length) (baseStart_5244899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5244899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5244899 prefixEnd_5244899 := by exact prefixLift 5244899
  have htrace : WordTrace (prefixWord ++ tailWord_5244899) baseStart_5244899 baseEnd_5244899 := by
    simpa [prefixWord, tailWord_5244899, baseEnd_5244899] using wordTrace_append hprefix tailTrace_5244899
  have hstable : (prefixWord ++ tailWord_5244899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5244899).length < 2 ^ (prefixWord ++ tailWord_5244899).sum := by decide
  have hdescent : baseEnd_5244899 < baseStart_5244899 := by decide
  rcases family_descends (prefixWord ++ tailWord_5244899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5244909 : List Nat := [1, 5, 1, 4, 2, 1, 1, 1, 1, 6]
def baseStart_5244909 : Nat := 118140960795 + 5244909 * 2 ^ 59
def prefixEnd_5244909 : Nat := 4983230072969 + 3 ^ 40 * 5244909 * 2
def baseEnd_5244909 : Nat := 897719768697508334372203

theorem tailTrace_5244909 : CollatzResearch.WordTrace tailWord_5244909 prefixEnd_5244909 897719768697508334372203 := by
  unfold tailWord_5244909
  simp only [CollatzResearch.WordTrace]
  refine ⟨191297546955597926987281781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127531697970398617991521187 191297546955597926987281781)
  ·
    refine ⟨17934145027087305655057667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 191297546955597926987281781 17934145027087305655057667)
    ·
      refine ⟨26901217540630958482586501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17934145027087305655057667 26901217540630958482586501)
      ·
        refine ⟨5043978288868304715484969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26901217540630958482586501 5043978288868304715484969)
        ·
          refine ⟨3782983716651228536613727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5043978288868304715484969 3782983716651228536613727)
          ·
            refine ⟨5674475574976842804920591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3782983716651228536613727 5674475574976842804920591)
            ·
              refine ⟨8511713362465264207380887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5674475574976842804920591 8511713362465264207380887)
              ·
                refine ⟨12767570043697896311071331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8511713362465264207380887 12767570043697896311071331)
                ·
                  refine ⟨19151355065546844466606997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12767570043697896311071331 19151355065546844466606997)
                  ·
                    refine ⟨897719768697508334372203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19151355065546844466606997 897719768697508334372203)
                    ·
                      rfl

theorem cell23_5244909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 1, 1, 6].length) (baseStart_5244909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5244909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5244909 prefixEnd_5244909 := by exact prefixLift 5244909
  have htrace : WordTrace (prefixWord ++ tailWord_5244909) baseStart_5244909 baseEnd_5244909 := by
    simpa [prefixWord, tailWord_5244909, baseEnd_5244909] using wordTrace_append hprefix tailTrace_5244909
  have hstable : (prefixWord ++ tailWord_5244909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5244909).length < 2 ^ (prefixWord ++ tailWord_5244909).sum := by decide
  have hdescent : baseEnd_5244909 < baseStart_5244909 := by decide
  rcases family_descends (prefixWord ++ tailWord_5244909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5244915 : List Nat := [1, 1, 1, 2, 2, 2, 1, 7, 2, 1, 3]
def baseStart_5244915 : Nat := 118140960795 + 5244915 * 2 ^ 59
def prefixEnd_5244915 : Nat := 4983230072969 + 3 ^ 40 * 5244915 * 2
def baseEnd_5244915 : Nat := 2693162386976451979641581

theorem tailTrace_5244915 : CollatzResearch.WordTrace tailWord_5244915 prefixEnd_5244915 2693162386976451979641581 := by
  unfold tailWord_5244915
  simp only [CollatzResearch.WordTrace]
  refine ⟨191297765793576190012000199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127531843862384126674666799 191297765793576190012000199)
  ·
    refine ⟨286946648690364285018000299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191297765793576190012000199 286946648690364285018000299)
    ·
      refine ⟨430419973035546427527000449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286946648690364285018000299 430419973035546427527000449)
      ·
        refine ⟨322814979776659820645250337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 430419973035546427527000449 322814979776659820645250337)
        ·
          refine ⟨242111234832494865483937753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 322814979776659820645250337 242111234832494865483937753)
          ·
            refine ⟨181583426124371149112953315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 242111234832494865483937753 181583426124371149112953315)
            ·
              refine ⟨272375139186556723669429973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181583426124371149112953315 272375139186556723669429973)
              ·
                refine ⟨6383792324684923211002265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 272375139186556723669429973 6383792324684923211002265)
                ·
                  refine ⟨4787844243513692408251699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6383792324684923211002265 4787844243513692408251699)
                  ·
                    refine ⟨7181766365270538612377549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4787844243513692408251699 7181766365270538612377549)
                    ·
                      refine ⟨2693162386976451979641581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7181766365270538612377549 2693162386976451979641581)
                      ·
                        rfl

theorem cell23_5244915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 7, 2, 1, 3].length) (baseStart_5244915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5244915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5244915 prefixEnd_5244915 := by exact prefixLift 5244915
  have htrace : WordTrace (prefixWord ++ tailWord_5244915) baseStart_5244915 baseEnd_5244915 := by
    simpa [prefixWord, tailWord_5244915, baseEnd_5244915] using wordTrace_append hprefix tailTrace_5244915
  have hstable : (prefixWord ++ tailWord_5244915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5244915).length < 2 ^ (prefixWord ++ tailWord_5244915).sum := by decide
  have hdescent : baseEnd_5244915 < baseStart_5244915 := by decide
  rcases family_descends (prefixWord ++ tailWord_5244915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5244925 : List Nat := [1, 4, 1, 1, 1, 2, 2, 3, 3, 3, 2]
def baseStart_5244925 : Nat := 118140960795 + 5244925 * 2 ^ 59
def prefixEnd_5244925 : Nat := 4983230072969 + 3 ^ 40 * 5244925 * 2
def baseEnd_5244925 : Nat := 2693167521782996940516535

theorem tailTrace_5244925 : CollatzResearch.WordTrace tailWord_5244925 prefixEnd_5244925 2693167521782996940516535 := by
  unfold tailWord_5244925
  simp only [CollatzResearch.WordTrace]
  refine ⟨191298130523539961719864229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127532087015693307813242819 191298130523539961719864229)
  ·
    refine ⟨35868399473163742822474543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 191298130523539961719864229 35868399473163742822474543)
    ·
      refine ⟨53802599209745614233711815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35868399473163742822474543 53802599209745614233711815)
      ·
        refine ⟨80703898814618421350567723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53802599209745614233711815 80703898814618421350567723)
        ·
          refine ⟨121055848221927632025851585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80703898814618421350567723 121055848221927632025851585)
          ·
            refine ⟨90791886166445724019388689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121055848221927632025851585 90791886166445724019388689)
            ·
              refine ⟨68093914624834293014541517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90791886166445724019388689 68093914624834293014541517)
              ·
                refine ⟨25535217984312859880453069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68093914624834293014541517 25535217984312859880453069)
                ·
                  refine ⟨9575706744117322455169901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25535217984312859880453069 9575706744117322455169901)
                  ·
                    refine ⟨3590890029043995920688713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9575706744117322455169901 3590890029043995920688713)
                    ·
                      refine ⟨2693167521782996940516535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3590890029043995920688713 2693167521782996940516535)
                      ·
                        rfl

theorem cell23_5244925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 3, 3, 2].length) (baseStart_5244925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5244925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5244925 prefixEnd_5244925 := by exact prefixLift 5244925
  have htrace : WordTrace (prefixWord ++ tailWord_5244925) baseStart_5244925 baseEnd_5244925 := by
    simpa [prefixWord, tailWord_5244925, baseEnd_5244925] using wordTrace_append hprefix tailTrace_5244925
  have hstable : (prefixWord ++ tailWord_5244925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5244925).length < 2 ^ (prefixWord ++ tailWord_5244925).sum := by decide
  have hdescent : baseEnd_5244925 < baseStart_5244925 := by decide
  rcases family_descends (prefixWord ++ tailWord_5244925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5244931 : List Nat := [1, 1, 1, 3, 2, 1, 1, 4, 1, 8]
def baseStart_5244931 : Nat := 118140960795 + 5244931 * 2 ^ 59
def prefixEnd_5244931 : Nat := 4983230072969 + 3 ^ 40 * 5244931 * 2
def baseEnd_5244931 : Nat := 897723534222307972347169

theorem tailTrace_5244931 : CollatzResearch.WordTrace tailWord_5244931 prefixEnd_5244931 897723534222307972347169 := by
  unfold tailWord_5244931
  simp only [CollatzResearch.WordTrace]
  refine ⟨191298349361518224744582647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127532232907678816496388431 191298349361518224744582647)
  ·
    refine ⟨286947524042277337116873971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191298349361518224744582647 286947524042277337116873971)
    ·
      refine ⟨430421286063416005675310957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286947524042277337116873971 430421286063416005675310957)
      ·
        refine ⟨161407982273781002128241609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 430421286063416005675310957 161407982273781002128241609)
        ·
          refine ⟨121055986705335751596181207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161407982273781002128241609 121055986705335751596181207)
          ·
            refine ⟨181583980058003627394271811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121055986705335751596181207 181583980058003627394271811)
            ·
              refine ⟨272375970087005441091407717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181583980058003627394271811 272375970087005441091407717)
              ·
                refine ⟨51070494391313520204638947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 272375970087005441091407717 51070494391313520204638947)
                ·
                  refine ⟨76605741586970280306958421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51070494391313520204638947 76605741586970280306958421)
                  ·
                    refine ⟨897723534222307972347169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 76605741586970280306958421 897723534222307972347169)
                    ·
                      rfl

theorem cell23_5244931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 8].length) (baseStart_5244931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5244931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5244931 prefixEnd_5244931 := by exact prefixLift 5244931
  have htrace : WordTrace (prefixWord ++ tailWord_5244931) baseStart_5244931 baseEnd_5244931 := by
    simpa [prefixWord, tailWord_5244931, baseEnd_5244931] using wordTrace_append hprefix tailTrace_5244931
  have hstable : (prefixWord ++ tailWord_5244931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5244931).length < 2 ^ (prefixWord ++ tailWord_5244931).sum := by decide
  have hdescent : baseEnd_5244931 < baseStart_5244931 := by decide
  rcases family_descends (prefixWord ++ tailWord_5244931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5244942 : List Nat := [4, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2]
def baseStart_5244942 : Nat := 118140960795 + 5244942 * 2 ^ 59
def prefixEnd_5244942 : Nat := 4983230072969 + 3 ^ 40 * 5244942 * 2
def baseEnd_5244942 : Nat := 2693176250954123374003957

theorem tailTrace_5244942 : CollatzResearch.WordTrace tailWord_5244942 prefixEnd_5244942 2693176250954123374003957 := by
  unfold tailWord_5244942
  simp only [CollatzResearch.WordTrace]
  refine ⟨23912343820559796702904135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127532500376318915748822053 23912343820559796702904135)
  ·
    refine ⟨35868515730839695054356203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23912343820559796702904135 35868515730839695054356203)
    ·
      refine ⟨53802773596259542581534305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35868515730839695054356203 53802773596259542581534305)
      ·
        refine ⟨40352080197194656936150729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53802773596259542581534305 40352080197194656936150729)
        ·
          refine ⟨30264060147895992702113047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40352080197194656936150729 30264060147895992702113047)
          ·
            refine ⟨45396090221843989053169571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30264060147895992702113047 45396090221843989053169571)
            ·
              refine ⟨68094135332765983579754357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45396090221843989053169571 68094135332765983579754357)
              ·
                refine ⟨6383825187446810960601971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68094135332765983579754357 6383825187446810960601971)
                ·
                  refine ⟨9575737781170216440902957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6383825187446810960601971 9575737781170216440902957)
                  ·
                    refine ⟨3590901667938831165338609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9575737781170216440902957 3590901667938831165338609)
                    ·
                      refine ⟨2693176250954123374003957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3590901667938831165338609 2693176250954123374003957)
                      ·
                        rfl

theorem cell23_5244942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2].length) (baseStart_5244942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5244942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5244942 prefixEnd_5244942 := by exact prefixLift 5244942
  have htrace : WordTrace (prefixWord ++ tailWord_5244942) baseStart_5244942 baseEnd_5244942 := by
    simpa [prefixWord, tailWord_5244942, baseEnd_5244942] using wordTrace_append hprefix tailTrace_5244942
  have hstable : (prefixWord ++ tailWord_5244942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5244942).length < 2 ^ (prefixWord ++ tailWord_5244942).sum := by decide
  have hdescent : baseEnd_5244942 < baseStart_5244942 := by decide
  rcases family_descends (prefixWord ++ tailWord_5244942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5245015 : List Nat := [1, 1, 3, 2, 2, 1, 3, 1, 2, 5, 2]
def baseStart_5245015 : Nat := 118140960795 + 5245015 * 2 ^ 59
def prefixEnd_5245015 : Nat := 4983230072969 + 3 ^ 40 * 5245015 * 2
def baseEnd_5245015 : Nat := 2693213735041901588391121

theorem tailTrace_5245015 : CollatzResearch.WordTrace tailWord_5245015 prefixEnd_5245015 2693213735041901588391121 := by
  unfold tailWord_5245015
  simp only [CollatzResearch.WordTrace]
  refine ⟨191301413093213907090640499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127534275395475938060426999 191301413093213907090640499)
  ·
    refine ⟨286952119639820860635960749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191301413093213907090640499 286952119639820860635960749)
    ·
      refine ⟨107607044864932822738485281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 286952119639820860635960749 107607044864932822738485281)
      ·
        refine ⟨80705283648699617053863961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107607044864932822738485281 80705283648699617053863961)
        ·
          refine ⟨60528962736524712790397971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80705283648699617053863961 60528962736524712790397971)
          ·
            refine ⟨90793444104787069185596957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60528962736524712790397971 90793444104787069185596957)
            ·
              refine ⟨34047541539295150944598859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90793444104787069185596957 34047541539295150944598859)
              ·
                refine ⟨51071312308942726416898289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34047541539295150944598859 51071312308942726416898289)
                ·
                  refine ⟨38303484231707044812673717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51071312308942726416898289 38303484231707044812673717)
                  ·
                    refine ⟨3590951646722535451188161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38303484231707044812673717 3590951646722535451188161)
                    ·
                      refine ⟨2693213735041901588391121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3590951646722535451188161 2693213735041901588391121)
                      ·
                        rfl

theorem cell23_5245015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 5, 2].length) (baseStart_5245015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5245015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5245015 prefixEnd_5245015 := by exact prefixLift 5245015
  have htrace : WordTrace (prefixWord ++ tailWord_5245015) baseStart_5245015 baseEnd_5245015 := by
    simpa [prefixWord, tailWord_5245015, baseEnd_5245015] using wordTrace_append hprefix tailTrace_5245015
  have hstable : (prefixWord ++ tailWord_5245015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5245015).length < 2 ^ (prefixWord ++ tailWord_5245015).sum := by decide
  have hdescent : baseEnd_5245015 < baseStart_5245015 := by decide
  rcases family_descends (prefixWord ++ tailWord_5245015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5245018 : List Nat := [3, 1, 1, 2, 1, 1, 3, 3, 1, 2, 5]
def baseStart_5245018 : Nat := 118140960795 + 5245018 * 2 ^ 59
def prefixEnd_5245018 : Nat := 4983230072969 + 3 ^ 40 * 5245018 * 2
def baseEnd_5245018 : Nat := 2693215275483865076653607

theorem tailTrace_5245018 : CollatzResearch.WordTrace tailWord_5245018 prefixEnd_5245018 2693215275483865076653607 := by
  unfold tailWord_5245018
  simp only [CollatzResearch.WordTrace]
  refine ⟨47825380628050759650749927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127534348341468692401999805 47825380628050759650749927)
  ·
    refine ⟨71738070942076139476124891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47825380628050759650749927 71738070942076139476124891)
    ·
      refine ⟨107607106413114209214187337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71738070942076139476124891 107607106413114209214187337)
      ·
        refine ⟨80705329809835656910640503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107607106413114209214187337 80705329809835656910640503)
        ·
          refine ⟨121057994714753485365960755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80705329809835656910640503 121057994714753485365960755)
          ·
            refine ⟨181586992072130228048941133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121057994714753485365960755 181586992072130228048941133)
            ·
              refine ⟨68095122027048835518352925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 181586992072130228048941133 68095122027048835518352925)
              ·
                refine ⟨25535670760143313319382347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68095122027048835518352925 25535670760143313319382347)
                ·
                  refine ⟨38303506140214969979073521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25535670760143313319382347 38303506140214969979073521)
                  ·
                    refine ⟨28727629605161227484305141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38303506140214969979073521 28727629605161227484305141)
                    ·
                      refine ⟨2693215275483865076653607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28727629605161227484305141 2693215275483865076653607)
                      ·
                        rfl

theorem cell23_5245018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_5245018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5245018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5245018 prefixEnd_5245018 := by exact prefixLift 5245018
  have htrace : WordTrace (prefixWord ++ tailWord_5245018) baseStart_5245018 baseEnd_5245018 := by
    simpa [prefixWord, tailWord_5245018, baseEnd_5245018] using wordTrace_append hprefix tailTrace_5245018
  have hstable : (prefixWord ++ tailWord_5245018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5245018).length < 2 ^ (prefixWord ++ tailWord_5245018).sum := by decide
  have hdescent : baseEnd_5245018 < baseStart_5245018 := by decide
  rcases family_descends (prefixWord ++ tailWord_5245018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5245042 : List Nat := [3, 2, 1, 2, 2, 4, 1, 1, 2, 5]
def baseStart_5245042 : Nat := 118140960795 + 5245042 * 2 ^ 59
def prefixEnd_5245042 : Nat := 4983230072969 + 3 ^ 40 * 5245042 * 2
def baseEnd_5245042 : Nat := 897742533006524327584499

theorem tailTrace_5245042 : CollatzResearch.WordTrace tailWord_5245042 prefixEnd_5245042 897742533006524327584499 := by
  unfold tailWord_5245042
  simp only [CollatzResearch.WordTrace]
  refine ⟨47825599466029022675468345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127534931909410727134582253 47825599466029022675468345)
  ·
    refine ⟨35869199599521767006601259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47825599466029022675468345 35869199599521767006601259)
    ·
      refine ⟨53803799399282650509901889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35869199599521767006601259 53803799399282650509901889)
      ·
        refine ⟨40352849549461987882426417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53803799399282650509901889 40352849549461987882426417)
        ·
          refine ⟨30264637162096490911819813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40352849549461987882426417 30264637162096490911819813)
          ·
            refine ⟨5674619467893092045966215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30264637162096490911819813 5674619467893092045966215)
            ·
              refine ⟨8511929201839638068949323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5674619467893092045966215 8511929201839638068949323)
              ·
                refine ⟨12767893802759457103423985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8511929201839638068949323 12767893802759457103423985)
                ·
                  refine ⟨9575920352069592827567989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12767893802759457103423985 9575920352069592827567989)
                  ·
                    refine ⟨897742533006524327584499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9575920352069592827567989 897742533006524327584499)
                    ·
                      rfl

theorem cell23_5245042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 1, 2, 5].length) (baseStart_5245042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5245042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5245042 prefixEnd_5245042 := by exact prefixLift 5245042
  have htrace : WordTrace (prefixWord ++ tailWord_5245042) baseStart_5245042 baseEnd_5245042 := by
    simpa [prefixWord, tailWord_5245042, baseEnd_5245042] using wordTrace_append hprefix tailTrace_5245042
  have hstable : (prefixWord ++ tailWord_5245042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5245042).length < 2 ^ (prefixWord ++ tailWord_5245042).sum := by decide
  have hdescent : baseEnd_5245042 < baseStart_5245042 := by decide
  rcases family_descends (prefixWord ++ tailWord_5245042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5245065 : List Nat := [1, 2, 1, 1, 4, 2, 2, 1, 4, 2, 3]
def baseStart_5245065 : Nat := 118140960795 + 5245065 * 2 ^ 59
def prefixEnd_5245065 : Nat := 4983230072969 + 3 ^ 40 * 5245065 * 2
def baseEnd_5245065 : Nat := 2693239409074626392765891

theorem tailTrace_5245065 : CollatzResearch.WordTrace tailWord_5245065 prefixEnd_5245065 2693239409074626392765891 := by
  unfold tailWord_5245065
  simp only [CollatzResearch.WordTrace]
  refine ⟨191303236743032765629960649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127535491162021843753307099 191303236743032765629960649)
  ·
    refine ⟨143477427557274574222470487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191303236743032765629960649 143477427557274574222470487)
    ·
      refine ⟨215216141335911861333705731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143477427557274574222470487 215216141335911861333705731)
      ·
        refine ⟨322824212003867792000558597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215216141335911861333705731 322824212003867792000558597)
        ·
          refine ⟨60529539750725211000104737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 322824212003867792000558597 60529539750725211000104737)
          ·
            refine ⟨45397154813043908250078553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60529539750725211000104737 45397154813043908250078553)
            ·
              refine ⟨34047866109782931187558915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45397154813043908250078553 34047866109782931187558915)
              ·
                refine ⟨51071799164674396781338373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34047866109782931187558915 51071799164674396781338373)
                ·
                  refine ⟨9575962343376449396500945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51071799164674396781338373 9575962343376449396500945)
                  ·
                    refine ⟨7181971757532337047375709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9575962343376449396500945 7181971757532337047375709)
                    ·
                      refine ⟨2693239409074626392765891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7181971757532337047375709 2693239409074626392765891)
                      ·
                        rfl

theorem cell23_5245065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 4, 2, 3].length) (baseStart_5245065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5245065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5245065 prefixEnd_5245065 := by exact prefixLift 5245065
  have htrace : WordTrace (prefixWord ++ tailWord_5245065) baseStart_5245065 baseEnd_5245065 := by
    simpa [prefixWord, tailWord_5245065, baseEnd_5245065] using wordTrace_append hprefix tailTrace_5245065
  have hstable : (prefixWord ++ tailWord_5245065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5245065).length < 2 ^ (prefixWord ++ tailWord_5245065).sum := by decide
  have hdescent : baseEnd_5245065 < baseStart_5245065 := by decide
  rcases family_descends (prefixWord ++ tailWord_5245065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5245072 : List Nat := [2, 1, 1, 1, 1, 1, 5, 6, 1, 4]
def baseStart_5245072 : Nat := 118140960795 + 5245072 * 2 ^ 59
def prefixEnd_5245072 : Nat := 4983230072969 + 3 ^ 40 * 5245072 * 2
def baseEnd_5245072 : Nat := 897747667813069288459453

theorem tailTrace_5245072 : CollatzResearch.WordTrace tailWord_5245072 prefixEnd_5245072 897747667813069288459453 := by
  unfold tailWord_5245072
  simp only [CollatzResearch.WordTrace]
  refine ⟨95651746027003702912732735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127535661369338270550310313 95651746027003702912732735)
  ·
    refine ⟨143477619040505554369099103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95651746027003702912732735 143477619040505554369099103)
    ·
      refine ⟨215216428560758331553648655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143477619040505554369099103 215216428560758331553648655)
      ·
        refine ⟨322824642841137497330472983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215216428560758331553648655 322824642841137497330472983)
        ·
          refine ⟨484236964261706245995709475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322824642841137497330472983 484236964261706245995709475)
          ·
            refine ⟨726355446392559368993564213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 484236964261706245995709475 726355446392559368993564213)
            ·
              refine ⟨68095823099302440843146645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 726355446392559368993564213 68095823099302440843146645)
              ·
                refine ⟨3191991707779801914522499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 68095823099302440843146645 3191991707779801914522499)
                ·
                  refine ⟨4787987561669702871783749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3191991707779801914522499 4787987561669702871783749)
                  ·
                    refine ⟨897747667813069288459453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4787987561669702871783749 897747667813069288459453)
                    ·
                      rfl

theorem cell23_5245072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 6, 1, 4].length) (baseStart_5245072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5245072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5245072 prefixEnd_5245072 := by exact prefixLift 5245072
  have htrace : WordTrace (prefixWord ++ tailWord_5245072) baseStart_5245072 baseEnd_5245072 := by
    simpa [prefixWord, tailWord_5245072, baseEnd_5245072] using wordTrace_append hprefix tailTrace_5245072
  have hstable : (prefixWord ++ tailWord_5245072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5245072).length < 2 ^ (prefixWord ++ tailWord_5245072).sum := by decide
  have hdescent : baseEnd_5245072 < baseStart_5245072 := by decide
  rcases family_descends (prefixWord ++ tailWord_5245072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5245115 : List Nat := [1, 1, 1, 1, 1, 2, 5, 5, 1, 5]
def baseStart_5245115 : Nat := 118140960795 + 5245115 * 2 ^ 59
def prefixEnd_5245115 : Nat := 4983230072969 + 3 ^ 40 * 5245115 * 2
def baseEnd_5245115 : Nat := 897755027702450399046887

theorem tailTrace_5245115 : CollatzResearch.WordTrace tailWord_5245115 prefixEnd_5245115 897755027702450399046887 := by
  unfold tailWord_5245115
  simp only [CollatzResearch.WordTrace]
  refine ⟨191305060392851624169280799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127536706928567749446187199 191305060392851624169280799)
  ·
    refine ⟨286957590589277436253921199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191305060392851624169280799 286957590589277436253921199)
    ·
      refine ⟨430436385883916154380881799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286957590589277436253921199 430436385883916154380881799)
      ·
        refine ⟨645654578825874231571322699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 430436385883916154380881799 645654578825874231571322699)
        ·
          refine ⟨968481868238811347356984049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 645654578825874231571322699 968481868238811347356984049)
          ·
            refine ⟨726361401179108510517738037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 968481868238811347356984049 726361401179108510517738037)
            ·
              refine ⟨68096381360541422861037941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 726361401179108510517738037 68096381360541422861037941)
              ·
                refine ⟨6384035752550758393222307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68096381360541422861037941 6384035752550758393222307)
                ·
                  refine ⟨9576053628826137589833461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6384035752550758393222307 9576053628826137589833461)
                  ·
                    refine ⟨897755027702450399046887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9576053628826137589833461 897755027702450399046887)
                    ·
                      rfl

theorem cell23_5245115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 5, 1, 5].length) (baseStart_5245115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5245115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5245115 prefixEnd_5245115 := by exact prefixLift 5245115
  have htrace : WordTrace (prefixWord ++ tailWord_5245115) baseStart_5245115 baseEnd_5245115 := by
    simpa [prefixWord, tailWord_5245115, baseEnd_5245115] using wordTrace_append hprefix tailTrace_5245115
  have hstable : (prefixWord ++ tailWord_5245115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5245115).length < 2 ^ (prefixWord ++ tailWord_5245115).sum := by decide
  have hdescent : baseEnd_5245115 < baseStart_5245115 := by decide
  rcases family_descends (prefixWord ++ tailWord_5245115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5245135 : List Nat := [1, 1, 2, 1, 1, 3, 4, 2, 3, 1, 4]
def baseStart_5245135 : Nat := 118140960795 + 5245135 * 2 ^ 59
def prefixEnd_5245135 : Nat := 4983230072969 + 3 ^ 40 * 5245135 * 2
def baseEnd_5245135 : Nat := 2693275352720441118890569

theorem tailTrace_5245135 : CollatzResearch.WordTrace tailWord_5245135 prefixEnd_5245135 2693275352720441118890569 := by
  unfold tailWord_5245135
  simp only [CollatzResearch.WordTrace]
  refine ⟨191305789852779167585008859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127537193235186111723339239 191305789852779167585008859)
  ·
    refine ⟨286958684779168751377513289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191305789852779167585008859 286958684779168751377513289)
    ·
      refine ⟨215219013584376563533134967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286958684779168751377513289 215219013584376563533134967)
      ·
        refine ⟨322828520376564845299702451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215219013584376563533134967 322828520376564845299702451)
        ·
          refine ⟨484242780564847267949553677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322828520376564845299702451 484242780564847267949553677)
          ·
            refine ⟨181591042711817725481082629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 484242780564847267949553677 181591042711817725481082629)
            ·
              refine ⟨34048320508465823527702993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 181591042711817725481082629 34048320508465823527702993)
              ·
                refine ⟨25536240381349367645777245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34048320508465823527702993 25536240381349367645777245)
                ·
                  refine ⟨9576090143006012867166467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25536240381349367645777245 9576090143006012867166467)
                  ·
                    refine ⟨14364135214509019300749701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9576090143006012867166467 14364135214509019300749701)
                    ·
                      refine ⟨2693275352720441118890569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14364135214509019300749701 2693275352720441118890569)
                      ·
                        rfl

theorem cell23_5245135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 3, 1, 4].length) (baseStart_5245135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5245135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5245135 prefixEnd_5245135 := by exact prefixLift 5245135
  have htrace : WordTrace (prefixWord ++ tailWord_5245135) baseStart_5245135 baseEnd_5245135 := by
    simpa [prefixWord, tailWord_5245135, baseEnd_5245135] using wordTrace_append hprefix tailTrace_5245135
  have hstable : (prefixWord ++ tailWord_5245135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5245135).length < 2 ^ (prefixWord ++ tailWord_5245135).sum := by decide
  have hdescent : baseEnd_5245135 < baseStart_5245135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5245135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5245149 : List Nat := [1, 4, 3, 2, 1, 1, 3, 2, 1, 5]
def baseStart_5245149 : Nat := 118140960795 + 5245149 * 2 ^ 59
def prefixEnd_5245149 : Nat := 4983230072969 + 3 ^ 40 * 5245149 * 2
def baseEnd_5245149 : Nat := 897760847149868021371835

theorem tailTrace_5245149 : CollatzResearch.WordTrace tailWord_5245149 prefixEnd_5245149 897760847149868021371835 := by
  unfold tailWord_5245149
  simp only [CollatzResearch.WordTrace]
  refine ⟨191306300474728447976018501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127537533649818965317345667 191306300474728447976018501)
  ·
    refine ⟨35869931339011583995503469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 191306300474728447976018501 35869931339011583995503469)
    ·
      refine ⟨13451224252129343998313801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35869931339011583995503469 13451224252129343998313801)
      ·
        refine ⟨10088418189097007998735351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13451224252129343998313801 10088418189097007998735351)
        ·
          refine ⟨15132627283645511998103027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10088418189097007998735351 15132627283645511998103027)
          ·
            refine ⟨22698940925468267997154541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15132627283645511998103027 22698940925468267997154541)
            ·
              refine ⟨8512102847050600498932953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22698940925468267997154541 8512102847050600498932953)
              ·
                refine ⟨6384077135287950374199715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8512102847050600498932953 6384077135287950374199715)
                ·
                  refine ⟨9576115702931925561299573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6384077135287950374199715 9576115702931925561299573)
                  ·
                    refine ⟨897760847149868021371835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9576115702931925561299573 897760847149868021371835)
                    ·
                      rfl

theorem cell23_5245149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_5245149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5245149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5245149 prefixEnd_5245149 := by exact prefixLift 5245149
  have htrace : WordTrace (prefixWord ++ tailWord_5245149) baseStart_5245149 baseEnd_5245149 := by
    simpa [prefixWord, tailWord_5245149, baseEnd_5245149] using wordTrace_append hprefix tailTrace_5245149
  have hstable : (prefixWord ++ tailWord_5245149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5245149).length < 2 ^ (prefixWord ++ tailWord_5245149).sum := by decide
  have hdescent : baseEnd_5245149 < baseStart_5245149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5245149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5245182 : List Nat := [4, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4]
def baseStart_5245182 : Nat := 118140960795 + 5245182 * 2 ^ 59
def prefixEnd_5245182 : Nat := 4983230072969 + 3 ^ 40 * 5245182 * 2
def baseEnd_5245182 : Nat := 2693299486311202435002853

theorem tailTrace_5245182 : CollatzResearch.WordTrace tailWord_5245182 prefixEnd_5245182 2693299486311202435002853 := by
  unfold tailWord_5245182
  simp only [CollatzResearch.WordTrace]
  refine ⟨23913438010451111826496225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127538336055739263074646533 23913438010451111826496225)
  ·
    refine ⟨17935078507838333869872169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23913438010451111826496225 17935078507838333869872169)
    ·
      refine ⟨13451308880878750402404127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17935078507838333869872169 13451308880878750402404127)
      ·
        refine ⟨20176963321318125603606191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13451308880878750402404127 20176963321318125603606191)
        ·
          refine ⟨30265444981977188405409287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20176963321318125603606191 30265444981977188405409287)
          ·
            refine ⟨45398167472965782608113931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30265444981977188405409287 45398167472965782608113931)
            ·
              refine ⟨68097251209448673912170897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45398167472965782608113931 68097251209448673912170897)
              ·
                refine ⟨51072938407086505434128173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68097251209448673912170897 51072938407086505434128173)
                ·
                  refine ⟨19152351902657439537798065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51072938407086505434128173 19152351902657439537798065)
                  ·
                    refine ⟨14364263926993079653348549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19152351902657439537798065 14364263926993079653348549)
                    ·
                      refine ⟨2693299486311202435002853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14364263926993079653348549 2693299486311202435002853)
                      ·
                        rfl

theorem cell23_5245182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_5245182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5245182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5245182 prefixEnd_5245182 := by exact prefixLift 5245182
  have htrace : WordTrace (prefixWord ++ tailWord_5245182) baseStart_5245182 baseEnd_5245182 := by
    simpa [prefixWord, tailWord_5245182, baseEnd_5245182] using wordTrace_append hprefix tailTrace_5245182
  have hstable : (prefixWord ++ tailWord_5245182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5245182).length < 2 ^ (prefixWord ++ tailWord_5245182).sum := by decide
  have hdescent : baseEnd_5245182 < baseStart_5245182 := by decide
  rcases family_descends (prefixWord ++ tailWord_5245182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5245192 : List Nat := [2, 1, 3, 2, 3, 3, 1, 8]
def baseStart_5245192 : Nat := 118140960795 + 5245192 * 2 ^ 59
def prefixEnd_5245192 : Nat := 4983230072969 + 3 ^ 40 * 5245192 * 2
def baseEnd_5245192 : Nat := 99752023004361014662141

theorem tailTrace_5245192 : CollatzResearch.WordTrace tailWord_5245192 prefixEnd_5245192 99752023004361014662141 := by
  unfold tailWord_5245192
  simp only [CollatzResearch.WordTrace]
  refine ⟨95653934406786333159916915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127538579209048444213222553 95653934406786333159916915)
  ·
    refine ⟨143480901610179499739875373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95653934406786333159916915 143480901610179499739875373)
    ·
      refine ⟨53805338103817312402453265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143480901610179499739875373 53805338103817312402453265)
      ·
        refine ⟨40354003577862984301839949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53805338103817312402453265 40354003577862984301839949)
        ·
          refine ⟨15132751341698619113189981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40354003577862984301839949 15132751341698619113189981)
          ·
            refine ⟨5674781753136982167446243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15132751341698619113189981 5674781753136982167446243)
            ·
              refine ⟨8512172629705473251169365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5674781753136982167446243 8512172629705473251169365)
              ·
                refine ⟨99752023004361014662141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8512172629705473251169365 99752023004361014662141)
                ·
                  rfl

theorem cell23_5245192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 8].length) (baseStart_5245192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5245192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5245192 prefixEnd_5245192 := by exact prefixLift 5245192
  have htrace : WordTrace (prefixWord ++ tailWord_5245192) baseStart_5245192 baseEnd_5245192 := by
    simpa [prefixWord, tailWord_5245192, baseEnd_5245192] using wordTrace_append hprefix tailTrace_5245192
  have hstable : (prefixWord ++ tailWord_5245192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5245192).length < 2 ^ (prefixWord ++ tailWord_5245192).sum := by decide
  have hdescent : baseEnd_5245192 < baseStart_5245192 := by decide
  rcases family_descends (prefixWord ++ tailWord_5245192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5245230 : List Nat := [4, 1, 3, 3, 2, 1, 1, 2, 2, 4]
def baseStart_5245230 : Nat := 118140960795 + 5245230 * 2 ^ 59
def prefixEnd_5245230 : Nat := 4983230072969 + 3 ^ 40 * 5245230 * 2
def baseEnd_5245230 : Nat := 897774711127539415734211

theorem tailTrace_5245230 : CollatzResearch.WordTrace tailWord_5245230 prefixEnd_5245230 897774711127539415734211 := by
  unfold tailWord_5245230
  simp only [CollatzResearch.WordTrace]
  refine ⟨23913656848429374851214643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127539503191623332539811429 23913656848429374851214643)
  ·
    refine ⟨35870485272644062276821965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23913656848429374851214643 35870485272644062276821965)
    ·
      refine ⟨13451431977241523353808237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35870485272644062276821965 13451431977241523353808237)
      ·
        refine ⟨5044286991465571257678089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13451431977241523353808237 5044286991465571257678089)
        ·
          refine ⟨3783215243599178443258567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5044286991465571257678089 3783215243599178443258567)
          ·
            refine ⟨5674822865398767664887851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3783215243599178443258567 5674822865398767664887851)
            ·
              refine ⟨8512234298098151497331777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5674822865398767664887851 8512234298098151497331777)
              ·
                refine ⟨6384175723573613622998833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8512234298098151497331777 6384175723573613622998833)
                ·
                  refine ⟨4788131792680210217249125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6384175723573613622998833 4788131792680210217249125)
                  ·
                    refine ⟨897774711127539415734211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4788131792680210217249125 897774711127539415734211)
                    ·
                      rfl

theorem cell23_5245230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_5245230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5245230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5245230 prefixEnd_5245230 := by exact prefixLift 5245230
  have htrace : WordTrace (prefixWord ++ tailWord_5245230) baseStart_5245230 baseEnd_5245230 := by
    simpa [prefixWord, tailWord_5245230, baseEnd_5245230] using wordTrace_append hprefix tailTrace_5245230
  have hstable : (prefixWord ++ tailWord_5245230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5245230).length < 2 ^ (prefixWord ++ tailWord_5245230).sum := by decide
  have hdescent : baseEnd_5245230 < baseStart_5245230 := by decide
  rcases family_descends (prefixWord ++ tailWord_5245230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5245235 : List Nat := [1, 1, 1, 2, 5, 1, 1, 1, 4, 6]
def baseStart_5245235 : Nat := 118140960795 + 5245235 * 2 ^ 59
def prefixEnd_5245235 : Nat := 4983230072969 + 3 ^ 40 * 5245235 * 2
def baseEnd_5245235 : Nat := 897775566928630242546703

theorem tailTrace_5245235 : CollatzResearch.WordTrace tailWord_5245235 prefixEnd_5245235 897775566928630242546703 := by
  unfold tailWord_5245235
  simp only [CollatzResearch.WordTrace]
  refine ⟨191309437152416884663649159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127539624768277923109099439 191309437152416884663649159)
  ·
    refine ⟨286964155728625326995473739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191309437152416884663649159 286964155728625326995473739)
    ·
      refine ⟨430446233592937990493210609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286964155728625326995473739 430446233592937990493210609)
      ·
        refine ⟨322834675194703492869907957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 430446233592937990493210609 322834675194703492869907957)
        ·
          refine ⟨30265750799503452456553871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 322834675194703492869907957 30265750799503452456553871)
          ·
            refine ⟨45398626199255178684830807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30265750799503452456553871 45398626199255178684830807)
            ·
              refine ⟨68097939298882768027246211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45398626199255178684830807 68097939298882768027246211)
              ·
                refine ⟨102146908948324152040869317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68097939298882768027246211 102146908948324152040869317)
                ·
                  refine ⟨19152545427810778507662997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 102146908948324152040869317 19152545427810778507662997)
                  ·
                    refine ⟨897775566928630242546703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19152545427810778507662997 897775566928630242546703)
                    ·
                      rfl

theorem cell23_5245235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 4, 6].length) (baseStart_5245235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5245235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5245235 prefixEnd_5245235 := by exact prefixLift 5245235
  have htrace : WordTrace (prefixWord ++ tailWord_5245235) baseStart_5245235 baseEnd_5245235 := by
    simpa [prefixWord, tailWord_5245235, baseEnd_5245235] using wordTrace_append hprefix tailTrace_5245235
  have hstable : (prefixWord ++ tailWord_5245235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5245235).length < 2 ^ (prefixWord ++ tailWord_5245235).sum := by decide
  have hdescent : baseEnd_5245235 < baseStart_5245235 := by decide
  rcases family_descends (prefixWord ++ tailWord_5245235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5245236 : List Nat := [2, 5, 1, 1, 1, 3, 1, 1, 4, 1, 3]
def baseStart_5245236 : Nat := 118140960795 + 5245236 * 2 ^ 59
def prefixEnd_5245236 : Nat := 4983230072969 + 3 ^ 40 * 5245236 * 2
def baseEnd_5245236 : Nat := 2693327214266545223727605

theorem tailTrace_5245236 : CollatzResearch.WordTrace tailWord_5245236 prefixEnd_5245236 2693327214266545223727605 := by
  unfold tailWord_5245236
  simp only [CollatzResearch.WordTrace]
  refine ⟨95654736812706630917217781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127539649083608841222957041 95654736812706630917217781)
  ·
    refine ⟨8967631576191246648489167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 95654736812706630917217781 8967631576191246648489167)
    ·
      refine ⟨13451447364286869972733751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8967631576191246648489167 13451447364286869972733751)
      ·
        refine ⟨20177171046430304959100627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13451447364286869972733751 20177171046430304959100627)
        ·
          refine ⟨30265756569645457438650941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20177171046430304959100627 30265756569645457438650941)
          ·
            refine ⟨11349658713617046539494103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30265756569645457438650941 11349658713617046539494103)
            ·
              refine ⟨17024488070425569809241155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11349658713617046539494103 17024488070425569809241155)
              ·
                refine ⟨25536732105638354713861733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17024488070425569809241155 25536732105638354713861733)
                ·
                  refine ⟨4788137269807191508849075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25536732105638354713861733 4788137269807191508849075)
                  ·
                    refine ⟨7182205904710787263273613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4788137269807191508849075 7182205904710787263273613)
                    ·
                      refine ⟨2693327214266545223727605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7182205904710787263273613 2693327214266545223727605)
                      ·
                        rfl

theorem cell23_5245236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_5245236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5245236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5245236 prefixEnd_5245236 := by exact prefixLift 5245236
  have htrace : WordTrace (prefixWord ++ tailWord_5245236) baseStart_5245236 baseEnd_5245236 := by
    simpa [prefixWord, tailWord_5245236, baseEnd_5245236] using wordTrace_append hprefix tailTrace_5245236
  have hstable : (prefixWord ++ tailWord_5245236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5245236).length < 2 ^ (prefixWord ++ tailWord_5245236).sum := by decide
  have hdescent : baseEnd_5245236 < baseStart_5245236 := by decide
  rcases family_descends (prefixWord ++ tailWord_5245236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5245295 : List Nat := [1, 1, 2, 1, 3, 1, 2, 2, 3, 7]
def baseStart_5245295 : Nat := 118140960795 + 5245295 * 2 ^ 59
def prefixEnd_5245295 : Nat := 4983230072969 + 3 ^ 40 * 5245295 * 2
def baseEnd_5245295 : Nat := 897785836541720164296611

theorem tailTrace_5245295 : CollatzResearch.WordTrace tailWord_5245295 prefixEnd_5245295 897785836541720164296611 := by
  unfold tailWord_5245295
  simp only [CollatzResearch.WordTrace]
  refine ⟨191311625532199514910833339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127541083688133009940555559 191311625532199514910833339)
  ·
    refine ⟨286967438298299272366250009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191311625532199514910833339 286967438298299272366250009)
    ·
      refine ⟨215225578723724454274687507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286967438298299272366250009 215225578723724454274687507)
      ·
        refine ⟨322838368085586681412031261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215225578723724454274687507 322838368085586681412031261)
        ·
          refine ⟨121064388032095005529511723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 322838368085586681412031261 121064388032095005529511723)
          ·
            refine ⟨181596582048142508294267585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121064388032095005529511723 181596582048142508294267585)
            ·
              refine ⟨136197436536106881220700689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 181596582048142508294267585 136197436536106881220700689)
              ·
                refine ⟨102148077402080160915525517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136197436536106881220700689 102148077402080160915525517)
                ·
                  refine ⟨38305529025780060343322069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102148077402080160915525517 38305529025780060343322069)
                  ·
                    refine ⟨897785836541720164296611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38305529025780060343322069 897785836541720164296611)
                    ·
                      rfl

theorem cell23_5245295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 7].length) (baseStart_5245295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5245295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5245295 prefixEnd_5245295 := by exact prefixLift 5245295
  have htrace : WordTrace (prefixWord ++ tailWord_5245295) baseStart_5245295 baseEnd_5245295 := by
    simpa [prefixWord, tailWord_5245295, baseEnd_5245295] using wordTrace_append hprefix tailTrace_5245295
  have hstable : (prefixWord ++ tailWord_5245295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5245295).length < 2 ^ (prefixWord ++ tailWord_5245295).sum := by decide
  have hdescent : baseEnd_5245295 < baseStart_5245295 := by decide
  rcases family_descends (prefixWord ++ tailWord_5245295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5245349 : List Nat := [1, 3, 1, 2, 1, 1, 4, 2, 2, 4, 2]
def baseStart_5245349 : Nat := 118140960795 + 5245349 * 2 ^ 59
def prefixEnd_5245349 : Nat := 4983230072969 + 3 ^ 40 * 5245349 * 2
def baseEnd_5245349 : Nat := 2693385237580503281614585

theorem tailTrace_5245349 : CollatzResearch.WordTrace tailWord_5245349 prefixEnd_5245349 2693385237580503281614585 := by
  unfold tailWord_5245349
  simp only [CollatzResearch.WordTrace]
  refine ⟨191313595074003882133299101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127542396716002588088866067 191313595074003882133299101)
  ·
    refine ⟨71742598152751455799987163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191313595074003882133299101 71742598152751455799987163)
    ·
      refine ⟨107613897229127183699980745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71742598152751455799987163 107613897229127183699980745)
      ·
        refine ⟨80710422921845387774985559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107613897229127183699980745 80710422921845387774985559)
        ·
          refine ⟨121065634382768081662478339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80710422921845387774985559 121065634382768081662478339)
          ·
            refine ⟨181598451574152122493717509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121065634382768081662478339 181598451574152122493717509)
            ·
              refine ⟨34049709670153522967572033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 181598451574152122493717509 34049709670153522967572033)
              ·
                refine ⟨25537282252615142225679025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34049709670153522967572033 25537282252615142225679025)
                ·
                  refine ⟨19152961689461356669259269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25537282252615142225679025 19152961689461356669259269)
                  ·
                    refine ⟨3591180316774004375486113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19152961689461356669259269 3591180316774004375486113)
                    ·
                      refine ⟨2693385237580503281614585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3591180316774004375486113 2693385237580503281614585)
                      ·
                        rfl

theorem cell23_5245349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 2, 4, 2].length) (baseStart_5245349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5245349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5245349 prefixEnd_5245349 := by exact prefixLift 5245349
  have htrace : WordTrace (prefixWord ++ tailWord_5245349) baseStart_5245349 baseEnd_5245349 := by
    simpa [prefixWord, tailWord_5245349, baseEnd_5245349] using wordTrace_append hprefix tailTrace_5245349
  have hstable : (prefixWord ++ tailWord_5245349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5245349).length < 2 ^ (prefixWord ++ tailWord_5245349).sum := by decide
  have hdescent : baseEnd_5245349 < baseStart_5245349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5245349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5245410 : List Nat := [3, 3, 3, 2, 1, 1, 2, 1, 3, 4]
def baseStart_5245410 : Nat := 118140960795 + 5245410 * 2 ^ 59
def prefixEnd_5245410 : Nat := 4983230072969 + 3 ^ 40 * 5245410 * 2
def baseEnd_5245410 : Nat := 897805519966809180983935

theorem tailTrace_5245410 : CollatzResearch.WordTrace tailWord_5245410 prefixEnd_5245410 897805519966809180983935 := by
  unfold tailWord_5245410
  simp only [CollatzResearch.WordTrace]
  refine ⟨47828954981695722387817421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127543879951188593034179789 47828954981695722387817421)
  ·
    refine ⟨17935858118135895895431533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47828954981695722387817421 17935858118135895895431533)
    ·
      refine ⟨6725946794300960960786825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17935858118135895895431533 6725946794300960960786825)
      ·
        refine ⟨5044460095725720720590119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6725946794300960960786825 5044460095725720720590119)
        ·
          refine ⟨7566690143588581080885179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5044460095725720720590119 7566690143588581080885179)
          ·
            refine ⟨11350035215382871621327769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7566690143588581080885179 11350035215382871621327769)
            ·
              refine ⟨8512526411537153715995827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11350035215382871621327769 8512526411537153715995827)
              ·
                refine ⟨12768789617305730573993741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8512526411537153715995827 12768789617305730573993741)
                ·
                  refine ⟨4788296106489648965247653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12768789617305730573993741 4788296106489648965247653)
                  ·
                    refine ⟨897805519966809180983935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4788296106489648965247653 897805519966809180983935)
                    ·
                      rfl

theorem cell23_5245410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_5245410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5245410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5245410 prefixEnd_5245410 := by exact prefixLift 5245410
  have htrace : WordTrace (prefixWord ++ tailWord_5245410) baseStart_5245410 baseEnd_5245410 := by
    simpa [prefixWord, tailWord_5245410, baseEnd_5245410] using wordTrace_append hprefix tailTrace_5245410
  have hstable : (prefixWord ++ tailWord_5245410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5245410).length < 2 ^ (prefixWord ++ tailWord_5245410).sum := by decide
  have hdescent : baseEnd_5245410 < baseStart_5245410 := by decide
  rcases family_descends (prefixWord ++ tailWord_5245410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5245416 : List Nat := [2, 1, 4, 1, 1, 3, 1, 3, 3, 1, 3]
def baseStart_5245416 : Nat := 118140960795 + 5245416 * 2 ^ 59
def prefixEnd_5245416 : Nat := 4983230072969 + 3 ^ 40 * 5245416 * 2
def baseEnd_5245416 : Nat := 2693419640784354519476777

theorem tailTrace_5245416 : CollatzResearch.WordTrace tailWord_5245416 prefixEnd_5245416 2693419640784354519476777 := by
  unfold tailWord_5245416
  simp only [CollatzResearch.WordTrace]
  refine ⟨95658019382380576287994051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127544025843174101717325401 95658019382380576287994051)
  ·
    refine ⟨143487029073570864431991077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95658019382380576287994051 143487029073570864431991077)
    ·
      refine ⟨26903817951294537080998327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 143487029073570864431991077 26903817951294537080998327)
      ·
        refine ⟨40355726926941805621497491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26903817951294537080998327 40355726926941805621497491)
        ·
          refine ⟨60533590390412708432246237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40355726926941805621497491 60533590390412708432246237)
          ·
            refine ⟨22700096396404765662092339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60533590390412708432246237 22700096396404765662092339)
            ·
              refine ⟨34050144594607148493138509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22700096396404765662092339 34050144594607148493138509)
              ·
                refine ⟨12768804222977680684926941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34050144594607148493138509 12768804222977680684926941)
                ·
                  refine ⟨4788301583616630256847603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12768804222977680684926941 4788301583616630256847603)
                  ·
                    refine ⟨7182452375424945385271405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4788301583616630256847603 7182452375424945385271405)
                    ·
                      refine ⟨2693419640784354519476777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7182452375424945385271405 2693419640784354519476777)
                      ·
                        rfl

theorem cell23_5245416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 3, 3, 1, 3].length) (baseStart_5245416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5245416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5245416 prefixEnd_5245416 := by exact prefixLift 5245416
  have htrace : WordTrace (prefixWord ++ tailWord_5245416) baseStart_5245416 baseEnd_5245416 := by
    simpa [prefixWord, tailWord_5245416, baseEnd_5245416] using wordTrace_append hprefix tailTrace_5245416
  have hstable : (prefixWord ++ tailWord_5245416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5245416).length < 2 ^ (prefixWord ++ tailWord_5245416).sum := by decide
  have hdescent : baseEnd_5245416 < baseStart_5245416 := by decide
  rcases family_descends (prefixWord ++ tailWord_5245416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5245439 : List Nat := [1, 1, 2, 2, 1, 2, 3, 1, 2, 6, 2]
def baseStart_5245439 : Nat := 118140960795 + 5245439 * 2 ^ 59
def prefixEnd_5245439 : Nat := 4983230072969 + 3 ^ 40 * 5245439 * 2
def baseEnd_5245439 : Nat := 2693431450839407929489171

theorem tailTrace_5245439 : CollatzResearch.WordTrace tailWord_5245439 prefixEnd_5245439 2693431450839407929489171 := by
  unfold tailWord_5245439
  simp only [CollatzResearch.WordTrace]
  refine ⟨191316877643677827504075371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127544585095785218336050247 191316877643677827504075371)
  ·
    refine ⟨286975316465516741256113057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191316877643677827504075371 286975316465516741256113057)
    ·
      refine ⟨215231487349137555942084793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286975316465516741256113057 215231487349137555942084793)
      ·
        refine ⟨161423615511853166956563595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215231487349137555942084793 161423615511853166956563595)
        ·
          refine ⟨242135423267779750434845393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161423615511853166956563595 242135423267779750434845393)
          ·
            refine ⟨181601567450834812826134045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 242135423267779750434845393 181601567450834812826134045)
            ·
              refine ⟨68100587794063054809800267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 181601567450834812826134045 68100587794063054809800267)
              ·
                refine ⟨102150881691094582214700401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68100587794063054809800267 102150881691094582214700401)
                ·
                  refine ⟨76613161268320936661025301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102150881691094582214700401 76613161268320936661025301)
                  ·
                    refine ⟨3591241934452543905985561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 76613161268320936661025301 3591241934452543905985561)
                    ·
                      refine ⟨2693431450839407929489171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3591241934452543905985561 2693431450839407929489171)
                      ·
                        rfl

theorem cell23_5245439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 6, 2].length) (baseStart_5245439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5245439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5245439 prefixEnd_5245439 := by exact prefixLift 5245439
  have htrace : WordTrace (prefixWord ++ tailWord_5245439) baseStart_5245439 baseEnd_5245439 := by
    simpa [prefixWord, tailWord_5245439, baseEnd_5245439] using wordTrace_append hprefix tailTrace_5245439
  have hstable : (prefixWord ++ tailWord_5245439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5245439).length < 2 ^ (prefixWord ++ tailWord_5245439).sum := by decide
  have hdescent : baseEnd_5245439 < baseStart_5245439 := by decide
  rcases family_descends (prefixWord ++ tailWord_5245439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5245459 : List Nat := [1, 1, 1, 2, 1, 5, 4, 1, 1, 1, 5]
def baseStart_5245459 : Nat := 118140960795 + 5245459 * 2 ^ 59
def prefixEnd_5245459 : Nat := 4983230072969 + 3 ^ 40 * 5245459 * 2
def baseEnd_5245459 : Nat := 2693441720452497851239079

theorem tailTrace_5245459 : CollatzResearch.WordTrace tailWord_5245459 prefixEnd_5245459 2693441720452497851239079 := by
  unfold tailWord_5245459
  simp only [CollatzResearch.WordTrace]
  refine ⟨191317607103605370919803431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127545071402403580613202287 191317607103605370919803431)
  ·
    refine ⟨286976410655408056379705147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191317607103605370919803431 286976410655408056379705147)
    ·
      refine ⟨430464615983112084569557721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286976410655408056379705147 430464615983112084569557721)
      ·
        refine ⟨322848461987334063427168291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 430464615983112084569557721 322848461987334063427168291)
        ·
          refine ⟨484272692981001095140752437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322848461987334063427168291 484272692981001095140752437)
          ·
            refine ⟨45400564966968852669445541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 484272692981001095140752437 45400564966968852669445541)
            ·
              refine ⟨8512605931306659875521039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45400564966968852669445541 8512605931306659875521039)
              ·
                refine ⟨12768908896959989813281559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8512605931306659875521039 12768908896959989813281559)
                ·
                  refine ⟨19153363345439984719922339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12768908896959989813281559 19153363345439984719922339)
                  ·
                    refine ⟨28730045018159977079883509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19153363345439984719922339 28730045018159977079883509)
                    ·
                      refine ⟨2693441720452497851239079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28730045018159977079883509 2693441720452497851239079)
                      ·
                        rfl

theorem cell23_5245459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 1, 1, 1, 5].length) (baseStart_5245459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5245459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5245459 prefixEnd_5245459 := by exact prefixLift 5245459
  have htrace : WordTrace (prefixWord ++ tailWord_5245459) baseStart_5245459 baseEnd_5245459 := by
    simpa [prefixWord, tailWord_5245459, baseEnd_5245459] using wordTrace_append hprefix tailTrace_5245459
  have hstable : (prefixWord ++ tailWord_5245459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5245459).length < 2 ^ (prefixWord ++ tailWord_5245459).sum := by decide
  have hdescent : baseEnd_5245459 < baseStart_5245459 := by decide
  rcases family_descends (prefixWord ++ tailWord_5245459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5245460 : List Nat := [2, 4, 3, 1, 1, 2, 1, 2, 2, 3, 2]
def baseStart_5245460 : Nat := 118140960795 + 5245460 * 2 ^ 59
def prefixEnd_5245460 : Nat := 4983230072969 + 3 ^ 40 * 5245460 * 2
def baseEnd_5245460 : Nat := 2693442233933152347326575

theorem tailTrace_5245460 : CollatzResearch.WordTrace tailWord_5245460 prefixEnd_5245460 2693442233933152347326575 := by
  unfold tailWord_5245460
  simp only [CollatzResearch.WordTrace]
  refine ⟨95658821788300874045294917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127545095717734498727059889 95658821788300874045294917)
  ·
    refine ⟨17936029085306413883492797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95658821788300874045294917 17936029085306413883492797)
    ·
      refine ⟨6726010906989905206309799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17936029085306413883492797 6726010906989905206309799)
      ·
        refine ⟨10089016360484857809464699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6726010906989905206309799 10089016360484857809464699)
        ·
          refine ⟨15133524540727286714197049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10089016360484857809464699 15133524540727286714197049)
          ·
            refine ⟨11350143405545465035647787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15133524540727286714197049 11350143405545465035647787)
            ·
              refine ⟨17025215108318197553471681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11350143405545465035647787 17025215108318197553471681)
              ·
                refine ⟨12768911331238648165103761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17025215108318197553471681 12768911331238648165103761)
                ·
                  refine ⟨9576683498428986123827821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12768911331238648165103761 9576683498428986123827821)
                  ·
                    refine ⟨3591256311910869796435433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9576683498428986123827821 3591256311910869796435433)
                    ·
                      refine ⟨2693442233933152347326575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3591256311910869796435433 2693442233933152347326575)
                      ·
                        rfl

theorem cell23_5245460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_5245460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5245460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5245460 prefixEnd_5245460 := by exact prefixLift 5245460
  have htrace : WordTrace (prefixWord ++ tailWord_5245460) baseStart_5245460 baseEnd_5245460 := by
    simpa [prefixWord, tailWord_5245460, baseEnd_5245460] using wordTrace_append hprefix tailTrace_5245460
  have hstable : (prefixWord ++ tailWord_5245460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5245460).length < 2 ^ (prefixWord ++ tailWord_5245460).sum := by decide
  have hdescent : baseEnd_5245460 < baseStart_5245460 := by decide
  rcases family_descends (prefixWord ++ tailWord_5245460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5245469 : List Nat := [1, 4, 2, 2, 1, 2, 1, 2, 1, 1, 6]
def baseStart_5245469 : Nat := 118140960795 + 5245469 * 2 ^ 59
def prefixEnd_5245469 : Nat := 4983230072969 + 3 ^ 40 * 5245469 * 2
def baseEnd_5245469 : Nat := 2693446855259042812114033

theorem tailTrace_5245469 : CollatzResearch.WordTrace tailWord_5245469 prefixEnd_5245469 2693446855259042812114033 := by
  unfold tailWord_5245469
  simp only [CollatzResearch.WordTrace]
  refine ⟨191317971833569142627667461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127545314555712761751778307 191317971833569142627667461)
  ·
    refine ⟨35872119718794214242687649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 191317971833569142627667461 35872119718794214242687649)
    ·
      refine ⟨26904089789095660682015737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35872119718794214242687649 26904089789095660682015737)
      ·
        refine ⟨20178067341821745511511803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26904089789095660682015737 20178067341821745511511803)
        ·
          refine ⟨30267101012732618267267705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20178067341821745511511803 30267101012732618267267705)
          ·
            refine ⟨22700325759549463700450779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30267101012732618267267705 22700325759549463700450779)
            ·
              refine ⟨34050488639324195550676169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22700325759549463700450779 34050488639324195550676169)
              ·
                refine ⟨25537866479493146663007127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34050488639324195550676169 25537866479493146663007127)
                ·
                  refine ⟨38306799719239719994510691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25537866479493146663007127 38306799719239719994510691)
                  ·
                    refine ⟨57460199578859579991766037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38306799719239719994510691 57460199578859579991766037)
                    ·
                      refine ⟨2693446855259042812114033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57460199578859579991766037 2693446855259042812114033)
                      ·
                        rfl

theorem cell23_5245469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_5245469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5245469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5245469 prefixEnd_5245469 := by exact prefixLift 5245469
  have htrace : WordTrace (prefixWord ++ tailWord_5245469) baseStart_5245469 baseEnd_5245469 := by
    simpa [prefixWord, tailWord_5245469, baseEnd_5245469] using wordTrace_append hprefix tailTrace_5245469
  have hstable : (prefixWord ++ tailWord_5245469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5245469).length < 2 ^ (prefixWord ++ tailWord_5245469).sum := by decide
  have hdescent : baseEnd_5245469 < baseStart_5245469 := by decide
  rcases family_descends (prefixWord ++ tailWord_5245469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5245510 : List Nat := [6, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5]
def baseStart_5245510 : Nat := 118140960795 + 5245510 * 2 ^ 59
def prefixEnd_5245510 : Nat := 4983230072969 + 3 ^ 40 * 5245510 * 2
def baseEnd_5245510 : Nat := 2693467907965877151701345

theorem tailTrace_5245510 : CollatzResearch.WordTrace tailWord_5245510 prefixEnd_5245510 2693467907965877151701345 := by
  unfold tailWord_5245510
  simp only [CollatzResearch.WordTrace]
  refine ⟨5978733350825643957184687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 127546311484280404419939989 5978733350825643957184687)
  ·
    refine ⟨8968100026238465935777031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5978733350825643957184687 8968100026238465935777031)
    ·
      refine ⟨13452150039357698903665547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8968100026238465935777031 13452150039357698903665547)
      ·
        refine ⟨20178225059036548355498321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13452150039357698903665547 20178225059036548355498321)
        ·
          refine ⟨15133668794277411266623741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20178225059036548355498321 15133668794277411266623741)
          ·
            refine ⟨5675125797854029224983903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15133668794277411266623741 5675125797854029224983903)
            ·
              refine ⟨8512688696781043837475855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5675125797854029224983903 8512688696781043837475855)
              ·
                refine ⟨12769033045171565756213783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8512688696781043837475855 12769033045171565756213783)
                ·
                  refine ⟨19153549567757348634320675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12769033045171565756213783 19153549567757348634320675)
                  ·
                    refine ⟨28730324351636022951481013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19153549567757348634320675 28730324351636022951481013)
                    ·
                      refine ⟨2693467907965877151701345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28730324351636022951481013 2693467907965877151701345)
                      ·
                        rfl

theorem cell23_5245510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_5245510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5245510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5245510 prefixEnd_5245510 := by exact prefixLift 5245510
  have htrace : WordTrace (prefixWord ++ tailWord_5245510) baseStart_5245510 baseEnd_5245510 := by
    simpa [prefixWord, tailWord_5245510, baseEnd_5245510] using wordTrace_append hprefix tailTrace_5245510
  have hstable : (prefixWord ++ tailWord_5245510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5245510).length < 2 ^ (prefixWord ++ tailWord_5245510).sum := by decide
  have hdescent : baseEnd_5245510 < baseStart_5245510 := by decide
  rcases family_descends (prefixWord ++ tailWord_5245510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5245524 : List Nat := [2, 4, 1, 1, 1, 5, 2, 2, 1, 2, 2]
def baseStart_5245524 : Nat := 118140960795 + 5245524 * 2 ^ 59
def prefixEnd_5245524 : Nat := 4983230072969 + 3 ^ 40 * 5245524 * 2
def baseEnd_5245524 : Nat := 2693475096695040096926281

theorem tailTrace_5245524 : CollatzResearch.WordTrace tailWord_5245524 prefixEnd_5245524 2693475096695040096926281 := by
  unfold tailWord_5245524
  simp only [CollatzResearch.WordTrace]
  refine ⟨95659988924184943510459813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127546651898913258013946417 95659988924184943510459813)
  ·
    refine ⟨17936247923284676908211215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95659988924184943510459813 17936247923284676908211215)
    ·
      refine ⟨26904371884927015362316823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17936247923284676908211215 26904371884927015362316823)
      ·
        refine ⟨40356557827390523043475235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26904371884927015362316823 40356557827390523043475235)
        ·
          refine ⟨60534836741085784565212853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40356557827390523043475235 60534836741085784565212853)
          ·
            refine ⟨5675140944476792302988705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60534836741085784565212853 5675140944476792302988705)
            ·
              refine ⟨4256355708357594227241529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5675140944476792302988705 4256355708357594227241529)
              ·
                refine ⟨3192266781268195670431147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4256355708357594227241529 3192266781268195670431147)
                ·
                  refine ⟨4788400171902293505646721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3192266781268195670431147 4788400171902293505646721)
                  ·
                    refine ⟨3591300128926720129235041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4788400171902293505646721 3591300128926720129235041)
                    ·
                      refine ⟨2693475096695040096926281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3591300128926720129235041 2693475096695040096926281)
                      ·
                        rfl

theorem cell23_5245524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 2, 2, 1, 2, 2].length) (baseStart_5245524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5245524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5245524 prefixEnd_5245524 := by exact prefixLift 5245524
  have htrace : WordTrace (prefixWord ++ tailWord_5245524) baseStart_5245524 baseEnd_5245524 := by
    simpa [prefixWord, tailWord_5245524, baseEnd_5245524] using wordTrace_append hprefix tailTrace_5245524
  have hstable : (prefixWord ++ tailWord_5245524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5245524).length < 2 ^ (prefixWord ++ tailWord_5245524).sum := by decide
  have hdescent : baseEnd_5245524 < baseStart_5245524 := by decide
  rcases family_descends (prefixWord ++ tailWord_5245524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5245539 : List Nat := [1, 1, 1, 5, 1, 2, 3, 1, 2, 6]
def baseStart_5245539 : Nat := 118140960795 + 5245539 * 2 ^ 59
def prefixEnd_5245539 : Nat := 4983230072969 + 3 ^ 40 * 5245539 * 2
def baseEnd_5245539 : Nat := 897827599634952512746237

theorem tailTrace_5245539 : CollatzResearch.WordTrace tailWord_5245539 prefixEnd_5245539 897827599634952512746237 := by
  unfold tailWord_5245539
  simp only [CollatzResearch.WordTrace]
  refine ⟨191320524943315544582715671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127547016628877029721810447 191320524943315544582715671)
  ·
    refine ⟨286980787414973316874073507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191320524943315544582715671 286980787414973316874073507)
    ·
      refine ⟨430471181122459975311110261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286980787414973316874073507 430471181122459975311110261)
      ·
        refine ⟨40356673230230622685416587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 430471181122459975311110261 40356673230230622685416587)
        ·
          refine ⟨60535009845345934028124881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40356673230230622685416587 60535009845345934028124881)
          ·
            refine ⟨45401257384009450521093661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60535009845345934028124881 45401257384009450521093661)
            ·
              refine ⟨17025471519003543945410123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45401257384009450521093661 17025471519003543945410123)
              ·
                refine ⟨25538207278505315918115185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17025471519003543945410123 25538207278505315918115185)
                ·
                  refine ⟨19153655458878986938586389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25538207278505315918115185 19153655458878986938586389)
                  ·
                    refine ⟨897827599634952512746237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19153655458878986938586389 897827599634952512746237)
                    ·
                      rfl

theorem cell23_5245539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 2, 6].length) (baseStart_5245539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5245539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5245539 prefixEnd_5245539 := by exact prefixLift 5245539
  have htrace : WordTrace (prefixWord ++ tailWord_5245539) baseStart_5245539 baseEnd_5245539 := by
    simpa [prefixWord, tailWord_5245539, baseEnd_5245539] using wordTrace_append hprefix tailTrace_5245539
  have hstable : (prefixWord ++ tailWord_5245539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5245539).length < 2 ^ (prefixWord ++ tailWord_5245539).sum := by decide
  have hdescent : baseEnd_5245539 < baseStart_5245539 := by decide
  rcases family_descends (prefixWord ++ tailWord_5245539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5245569 : List Nat := [1, 2, 4, 2, 1, 1, 1, 2, 9]
def baseStart_5245569 : Nat := 118140960795 + 5245569 * 2 ^ 59
def prefixEnd_5245569 : Nat := 4983230072969 + 3 ^ 40 * 5245569 * 2
def baseEnd_5245569 : Nat := 299277578147165824540397

theorem tailTrace_5245569 : CollatzResearch.WordTrace tailWord_5245569 prefixEnd_5245569 299277578147165824540397 := by
  unfold tailWord_5245569
  simp only [CollatzResearch.WordTrace]
  refine ⟨191321619133206859706307761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127547746088804573137538507 191321619133206859706307761)
  ·
    refine ⟨143491214349905144779730821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191321619133206859706307761 143491214349905144779730821)
    ·
      refine ⟨26904602690607214646199529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 143491214349905144779730821 26904602690607214646199529)
      ·
        refine ⟨20178452017955410984649647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26904602690607214646199529 20178452017955410984649647)
        ·
          refine ⟨30267678026933116476974471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20178452017955410984649647 30267678026933116476974471)
          ·
            refine ⟨45401517040399674715461707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30267678026933116476974471 45401517040399674715461707)
            ·
              refine ⟨68102275560599512073192561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45401517040399674715461707 68102275560599512073192561)
              ·
                refine ⟨51076706670449634054894421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68102275560599512073192561 51076706670449634054894421)
                ·
                  refine ⟨299277578147165824540397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 51076706670449634054894421 299277578147165824540397)
                  ·
                    rfl

theorem cell23_5245569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 9].length) (baseStart_5245569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5245569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5245569 prefixEnd_5245569 := by exact prefixLift 5245569
  have htrace : WordTrace (prefixWord ++ tailWord_5245569) baseStart_5245569 baseEnd_5245569 := by
    simpa [prefixWord, tailWord_5245569, baseEnd_5245569] using wordTrace_append hprefix tailTrace_5245569
  have hstable : (prefixWord ++ tailWord_5245569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5245569).length < 2 ^ (prefixWord ++ tailWord_5245569).sum := by decide
  have hdescent : baseEnd_5245569 < baseStart_5245569 := by decide
  rcases family_descends (prefixWord ++ tailWord_5245569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5245586 : List Nat := [3, 2, 3, 1, 2, 1, 1, 3, 7]
def baseStart_5245586 : Nat := 118140960795 + 5245586 * 2 ^ 59
def prefixEnd_5245586 : Nat := 4983230072969 + 3 ^ 40 * 5245586 * 2
def baseEnd_5245586 : Nat := 299278548055068761594555

theorem tailTrace_5245586 : CollatzResearch.WordTrace tailWord_5245586 prefixEnd_5245586 299278548055068761594555 := by
  unfold tailWord_5245586
  simp only [CollatzResearch.WordTrace]
  refine ⟨47830559793536317902419153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127548159449430181073117741 47830559793536317902419153)
  ·
    refine ⟨35872919845152238426814365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47830559793536317902419153 35872919845152238426814365)
    ·
      refine ⟨13452344941932089410055387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35872919845152238426814365 13452344941932089410055387)
      ·
        refine ⟨20178517412898134115083081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13452344941932089410055387 20178517412898134115083081)
        ·
          refine ⟨15133888059673600586312311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20178517412898134115083081 15133888059673600586312311)
          ·
            refine ⟨22700832089510400879468467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15133888059673600586312311 22700832089510400879468467)
            ·
              refine ⟨34051248134265601319202701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22700832089510400879468467 34051248134265601319202701)
              ·
                refine ⟨12769218050349600494701013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34051248134265601319202701 12769218050349600494701013)
                ·
                  refine ⟨299278548055068761594555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12769218050349600494701013 299278548055068761594555)
                  ·
                    rfl

theorem cell23_5245586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 3, 7].length) (baseStart_5245586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5245586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5245586 prefixEnd_5245586 := by exact prefixLift 5245586
  have htrace : WordTrace (prefixWord ++ tailWord_5245586) baseStart_5245586 baseEnd_5245586 := by
    simpa [prefixWord, tailWord_5245586, baseEnd_5245586] using wordTrace_append hprefix tailTrace_5245586
  have hstable : (prefixWord ++ tailWord_5245586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5245586).length < 2 ^ (prefixWord ++ tailWord_5245586).sum := by decide
  have hdescent : baseEnd_5245586 < baseStart_5245586 := by decide
  rcases family_descends (prefixWord ++ tailWord_5245586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5245639 : List Nat := [1, 1, 4, 1, 1, 1, 2, 1, 1, 5, 5]
def baseStart_5245639 : Nat := 118140960795 + 5245639 * 2 ^ 59
def prefixEnd_5245639 : Nat := 4983230072969 + 3 ^ 40 * 5245639 * 2
def baseEnd_5245639 : Nat := 2693534146970307146988251

theorem tailTrace_5245639 : CollatzResearch.WordTrace tailWord_5245639 prefixEnd_5245639 2693534146970307146988251 := by
  unfold tailWord_5245639
  simp only [CollatzResearch.WordTrace]
  refine ⟨191324172242953261661355971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127549448161968841107570647 191324172242953261661355971)
  ·
    refine ⟨286986258364429892492033957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191324172242953261661355971 286986258364429892492033957)
    ·
      refine ⟨53809923443330604842256367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 286986258364429892492033957 53809923443330604842256367)
      ·
        refine ⟨80714885164995907263384551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53809923443330604842256367 80714885164995907263384551)
        ·
          refine ⟨121072327747493860895076827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80714885164995907263384551 121072327747493860895076827)
          ·
            refine ⟨181608491621240791342615241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121072327747493860895076827 181608491621240791342615241)
            ·
              refine ⟨136206368715930593506961431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 181608491621240791342615241 136206368715930593506961431)
              ·
                refine ⟨204309553073895890260442147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136206368715930593506961431 204309553073895890260442147)
                ·
                  refine ⟨306464329610843835390663221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 204309553073895890260442147 306464329610843835390663221)
                  ·
                    refine ⟨28731030901016609567874677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 306464329610843835390663221 28731030901016609567874677)
                    ·
                      refine ⟨2693534146970307146988251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28731030901016609567874677 2693534146970307146988251)
                      ·
                        rfl

theorem cell23_5245639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_5245639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5245639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5245639 prefixEnd_5245639 := by exact prefixLift 5245639
  have htrace : WordTrace (prefixWord ++ tailWord_5245639) baseStart_5245639 baseEnd_5245639 := by
    simpa [prefixWord, tailWord_5245639, baseEnd_5245639] using wordTrace_append hprefix tailTrace_5245639
  have hstable : (prefixWord ++ tailWord_5245639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5245639).length < 2 ^ (prefixWord ++ tailWord_5245639).sum := by decide
  have hdescent : baseEnd_5245639 < baseStart_5245639 := by decide
  rcases family_descends (prefixWord ++ tailWord_5245639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5245706 : List Nat := [3, 1, 2, 2, 1, 2, 1, 1, 5, 5]
def baseStart_5245706 : Nat := 118140960795 + 5245706 * 2 ^ 59
def prefixEnd_5245706 : Nat := 4983230072969 + 3 ^ 40 * 5245706 * 2
def baseEnd_5245706 : Nat := 897856183391386128283481

theorem tailTrace_5245706 : CollatzResearch.WordTrace tailWord_5245706 prefixEnd_5245706 897856183391386128283481 := by
  unfold tailWord_5245706
  simp only [CollatzResearch.WordTrace]
  refine ⟨47831653983427633026011243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127551077289140354736029981 47831653983427633026011243)
  ·
    refine ⟨71747480975141449539016865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47831653983427633026011243 71747480975141449539016865)
    ·
      refine ⟨53810610731356087154262649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71747480975141449539016865 53810610731356087154262649)
      ·
        refine ⟨40357958048517065365696987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53810610731356087154262649 40357958048517065365696987)
        ·
          refine ⟨60536937072775598048545481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40357958048517065365696987 60536937072775598048545481)
          ·
            refine ⟨45402702804581698536409111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60536937072775598048545481 45402702804581698536409111)
            ·
              refine ⟨68104054206872547804613667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45402702804581698536409111 68104054206872547804613667)
              ·
                refine ⟨102156081310308821706920501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68104054206872547804613667 102156081310308821706920501)
                ·
                  refine ⟨9577132622841452035023797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 102156081310308821706920501 9577132622841452035023797)
                  ·
                    refine ⟨897856183391386128283481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9577132622841452035023797 897856183391386128283481)
                    ·
                      rfl

theorem cell23_5245706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 5, 5].length) (baseStart_5245706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5245706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5245706 prefixEnd_5245706 := by exact prefixLift 5245706
  have htrace : WordTrace (prefixWord ++ tailWord_5245706) baseStart_5245706 baseEnd_5245706 := by
    simpa [prefixWord, tailWord_5245706, baseEnd_5245706] using wordTrace_append hprefix tailTrace_5245706
  have hstable : (prefixWord ++ tailWord_5245706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5245706).length < 2 ^ (prefixWord ++ tailWord_5245706).sum := by decide
  have hdescent : baseEnd_5245706 < baseStart_5245706 := by decide
  rcases family_descends (prefixWord ++ tailWord_5245706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5245713 : List Nat := [1, 2, 2, 1, 1, 3, 2, 2, 4, 3, 2]
def baseStart_5245713 : Nat := 118140960795 + 5245713 * 2 ^ 59
def prefixEnd_5245713 : Nat := 4983230072969 + 3 ^ 40 * 5245713 * 2
def baseEnd_5245713 : Nat := 2693572144538739857462911

theorem tailTrace_5245713 : CollatzResearch.WordTrace tailWord_5245713 prefixEnd_5245713 2693572144538739857462911 := by
  unfold tailWord_5245713
  simp only [CollatzResearch.WordTrace]
  refine ⟨191326871244685172299549793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127551247496456781533033195 191326871244685172299549793)
  ·
    refine ⟨143495153433513879224662345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191326871244685172299549793 143495153433513879224662345)
    ·
      refine ⟨107621365075135409418496759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143495153433513879224662345 107621365075135409418496759)
      ·
        refine ⟨161432047612703114127745139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107621365075135409418496759 161432047612703114127745139)
        ·
          refine ⟨242148071419054671191617709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161432047612703114127745139 242148071419054671191617709)
          ·
            refine ⟨90805526782145501696856641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 242148071419054671191617709 90805526782145501696856641)
            ·
              refine ⟨68104145086609126272642481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90805526782145501696856641 68104145086609126272642481)
              ·
                refine ⟨51078108814956844704481861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68104145086609126272642481 51078108814956844704481861)
                ·
                  refine ⟨9577145402804408382090349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51078108814956844704481861 9577145402804408382090349)
                  ·
                    refine ⟨3591429526051653143283881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9577145402804408382090349 3591429526051653143283881)
                    ·
                      refine ⟨2693572144538739857462911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3591429526051653143283881 2693572144538739857462911)
                      ·
                        rfl

theorem cell23_5245713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 3, 2].length) (baseStart_5245713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5245713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5245713 prefixEnd_5245713 := by exact prefixLift 5245713
  have htrace : WordTrace (prefixWord ++ tailWord_5245713) baseStart_5245713 baseEnd_5245713 := by
    simpa [prefixWord, tailWord_5245713, baseEnd_5245713] using wordTrace_append hprefix tailTrace_5245713
  have hstable : (prefixWord ++ tailWord_5245713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5245713).length < 2 ^ (prefixWord ++ tailWord_5245713).sum := by decide
  have hdescent : baseEnd_5245713 < baseStart_5245713 := by decide
  rcases family_descends (prefixWord ++ tailWord_5245713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5245730 : List Nat := [3, 3, 1, 1, 2, 3, 1, 1, 1, 5, 2]
def baseStart_5245730 : Nat := 118140960795 + 5245730 * 2 ^ 59
def prefixEnd_5245730 : Nat := 4983230072969 + 3 ^ 40 * 5245730 * 2
def baseEnd_5245730 : Nat := 2693580873709866290950333

theorem tailTrace_5245730 : CollatzResearch.WordTrace tailWord_5245730 prefixEnd_5245730 2693580873709866290950333 := by
  unfold tailWord_5245730
  simp only [CollatzResearch.WordTrace]
  refine ⟨47831872821405896050729661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127551660857082389468612429 47831872821405896050729661)
  ·
    refine ⟨17936952308027211019023623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47831872821405896050729661 17936952308027211019023623)
    ·
      refine ⟨26905428462040816528535435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17936952308027211019023623 26905428462040816528535435)
      ·
        refine ⟨40358142693061224792803153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26905428462040816528535435 40358142693061224792803153)
        ·
          refine ⟨30268607019795918594602365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40358142693061224792803153 30268607019795918594602365)
          ·
            refine ⟨11350727632423469472975887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30268607019795918594602365 11350727632423469472975887)
            ·
              refine ⟨17026091448635204209463831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11350727632423469472975887 17026091448635204209463831)
              ·
                refine ⟨25539137172952806314195747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17026091448635204209463831 25539137172952806314195747)
                ·
                  refine ⟨38308705759429209471293621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25539137172952806314195747 38308705759429209471293621)
                  ·
                    refine ⟨3591441164946488387933777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38308705759429209471293621 3591441164946488387933777)
                    ·
                      refine ⟨2693580873709866290950333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3591441164946488387933777 2693580873709866290950333)
                      ·
                        rfl

theorem cell23_5245730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 1, 5, 2].length) (baseStart_5245730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5245730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5245730 prefixEnd_5245730 := by exact prefixLift 5245730
  have htrace : WordTrace (prefixWord ++ tailWord_5245730) baseStart_5245730 baseEnd_5245730 := by
    simpa [prefixWord, tailWord_5245730, baseEnd_5245730] using wordTrace_append hprefix tailTrace_5245730
  have hstable : (prefixWord ++ tailWord_5245730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5245730).length < 2 ^ (prefixWord ++ tailWord_5245730).sum := by decide
  have hdescent : baseEnd_5245730 < baseStart_5245730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5245730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5245756 : List Nat := [2, 2, 2, 2, 1, 1, 1, 4, 1, 1, 6]
def baseStart_5245756 : Nat := 118140960795 + 5245756 * 2 ^ 59
def prefixEnd_5245756 : Nat := 4983230072969 + 3 ^ 40 * 5245756 * 2
def baseEnd_5245756 : Nat := 2693594224206883189225213

theorem tailTrace_5245756 : CollatzResearch.WordTrace tailWord_5245756 prefixEnd_5245756 2693594224206883189225213 := by
  unfold tailWord_5245756
  simp only [CollatzResearch.WordTrace]
  refine ⟨95664219791764695321682561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127552293055686260428910081 95664219791764695321682561)
  ·
    refine ⟨71748164843823521491261921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95664219791764695321682561 71748164843823521491261921)
    ·
      refine ⟨53811123632867641118446441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71748164843823521491261921 53811123632867641118446441)
      ·
        refine ⟨40358342724650730838834831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53811123632867641118446441 40358342724650730838834831)
        ·
          refine ⟨60537514086976096258252247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40358342724650730838834831 60537514086976096258252247)
          ·
            refine ⟨90806271130464144387378371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60537514086976096258252247 90806271130464144387378371)
            ·
              refine ⟨136209406695696216581067557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90806271130464144387378371 136209406695696216581067557)
              ·
                refine ⟨25539263755443040608950167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 136209406695696216581067557 25539263755443040608950167)
                ·
                  refine ⟨38308895633164560913425251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25539263755443040608950167 38308895633164560913425251)
                  ·
                    refine ⟨57463343449746841370137877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38308895633164560913425251 57463343449746841370137877)
                    ·
                      refine ⟨2693594224206883189225213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57463343449746841370137877 2693594224206883189225213)
                      ·
                        rfl

theorem cell23_5245756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_5245756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5245756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5245756 prefixEnd_5245756 := by exact prefixLift 5245756
  have htrace : WordTrace (prefixWord ++ tailWord_5245756) baseStart_5245756 baseEnd_5245756 := by
    simpa [prefixWord, tailWord_5245756, baseEnd_5245756] using wordTrace_append hprefix tailTrace_5245756
  have hstable : (prefixWord ++ tailWord_5245756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5245756).length < 2 ^ (prefixWord ++ tailWord_5245756).sum := by decide
  have hdescent : baseEnd_5245756 < baseStart_5245756 := by decide
  rcases family_descends (prefixWord ++ tailWord_5245756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5245783 : List Nat := [1, 1, 3, 2, 4, 1, 4, 7]
def baseStart_5245783 : Nat := 118140960795 + 5245783 * 2 ^ 59
def prefixEnd_5245783 : Nat := 4983230072969 + 3 ^ 40 * 5245783 * 2
def baseEnd_5245783 : Nat := 99763262525353873466207

theorem tailTrace_5245783 : CollatzResearch.WordTrace tailWord_5245783 prefixEnd_5245783 99763262525353873466207 := by
  unfold tailWord_5245783
  simp only [CollatzResearch.WordTrace]
  refine ⟨191329424354431574254598003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127552949569621049503065335 191329424354431574254598003)
  ·
    refine ⟨286994136531647361381897005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191329424354431574254598003 286994136531647361381897005)
    ·
      refine ⟨107622801199367760518211377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 286994136531647361381897005 107622801199367760518211377)
      ·
        refine ⟨80717100899525820388658533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107622801199367760518211377 80717100899525820388658533)
        ·
          refine ⟨15134456418661091322873475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80717100899525820388658533 15134456418661091322873475)
          ·
            refine ⟨22701684627991636984310213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15134456418661091322873475 22701684627991636984310213)
            ·
              refine ⟨4256565867748431934558165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22701684627991636984310213 4256565867748431934558165)
              ·
                refine ⟨99763262525353873466207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4256565867748431934558165 99763262525353873466207)
                ·
                  rfl

theorem cell23_5245783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 4, 7].length) (baseStart_5245783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5245783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5245783 prefixEnd_5245783 := by exact prefixLift 5245783
  have htrace : WordTrace (prefixWord ++ tailWord_5245783) baseStart_5245783 baseEnd_5245783 := by
    simpa [prefixWord, tailWord_5245783, baseEnd_5245783] using wordTrace_append hprefix tailTrace_5245783
  have hstable : (prefixWord ++ tailWord_5245783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5245783).length < 2 ^ (prefixWord ++ tailWord_5245783).sum := by decide
  have hdescent : baseEnd_5245783 < baseStart_5245783 := by decide
  rcases family_descends (prefixWord ++ tailWord_5245783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5245810 : List Nat := [3, 2, 1, 2, 1, 1, 4, 1, 4, 1, 3]
def baseStart_5245810 : Nat := 118140960795 + 5245810 * 2 ^ 59
def prefixEnd_5245810 : Nat := 4983230072969 + 3 ^ 40 * 5245810 * 2
def baseEnd_5245810 : Nat := 2693621952162225977949965

theorem tailTrace_5245810 : CollatzResearch.WordTrace tailWord_5245810 prefixEnd_5245810 2693621952162225977949965 := by
  unfold tailWord_5245810
  simp only [CollatzResearch.WordTrace]
  refine ⟨47832602281333439466457721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127553606083555838577220589 47832602281333439466457721)
  ·
    refine ⟨35874451711000079599843291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47832602281333439466457721 35874451711000079599843291)
    ·
      refine ⟨53811677566500119399764937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35874451711000079599843291 53811677566500119399764937)
      ·
        refine ⟨40358758174875089549823703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53811677566500119399764937 40358758174875089549823703)
        ·
          refine ⟨60538137262312634324735555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40358758174875089549823703 60538137262312634324735555)
          ·
            refine ⟨90807205893468951487103333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60538137262312634324735555 90807205893468951487103333)
            ·
              refine ⟨17026351105025428403831875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90807205893468951487103333 17026351105025428403831875)
              ·
                refine ⟨25539526657538142605747813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17026351105025428403831875 25539526657538142605747813)
                ·
                  refine ⟨4788661248288401738577715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25539526657538142605747813 4788661248288401738577715)
                  ·
                    refine ⟨7182991872432602607866573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4788661248288401738577715 7182991872432602607866573)
                    ·
                      refine ⟨2693621952162225977949965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7182991872432602607866573 2693621952162225977949965)
                      ·
                        rfl

theorem cell23_5245810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 4, 1, 3].length) (baseStart_5245810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5245810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5245810 prefixEnd_5245810 := by exact prefixLift 5245810
  have htrace : WordTrace (prefixWord ++ tailWord_5245810) baseStart_5245810 baseEnd_5245810 := by
    simpa [prefixWord, tailWord_5245810, baseEnd_5245810] using wordTrace_append hprefix tailTrace_5245810
  have hstable : (prefixWord ++ tailWord_5245810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5245810).length < 2 ^ (prefixWord ++ tailWord_5245810).sum := by decide
  have hdescent : baseEnd_5245810 < baseStart_5245810 := by decide
  rcases family_descends (prefixWord ++ tailWord_5245810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5245853 : List Nat := [1, 4, 2, 1, 2, 1, 1, 3, 2, 1, 5]
def baseStart_5245853 : Nat := 118140960795 + 5245853 * 2 ^ 59
def prefixEnd_5245853 : Nat := 4983230072969 + 3 ^ 40 * 5245853 * 2
def baseEnd_5245853 : Nat := 2693644031830369309712267

theorem tailTrace_5245853 : CollatzResearch.WordTrace tailWord_5245853 prefixEnd_5245853 2693644031830369309712267 := by
  unfold tailWord_5245853
  simp only [CollatzResearch.WordTrace]
  refine ⟨191331977464177976209646213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127554651642785317473097475 191331977464177976209646213)
  ·
    refine ⟨35874745774533370539308665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 191331977464177976209646213 35874745774533370539308665)
    ·
      refine ⟨26906059330900027904481499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35874745774533370539308665 26906059330900027904481499)
      ·
        refine ⟨40359088996350041856722249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26906059330900027904481499 40359088996350041856722249)
        ·
          refine ⟨30269316747262531392541687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40359088996350041856722249 30269316747262531392541687)
          ·
            refine ⟨45403975120893797088812531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30269316747262531392541687 45403975120893797088812531)
            ·
              refine ⟨68105962681340695633218797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45403975120893797088812531 68105962681340695633218797)
              ·
                refine ⟨25539736005502760862457049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68105962681340695633218797 25539736005502760862457049)
                ·
                  refine ⟨19154802004127070646842787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25539736005502760862457049 19154802004127070646842787)
                  ·
                    refine ⟨28732203006190605970264181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19154802004127070646842787 28732203006190605970264181)
                    ·
                      refine ⟨2693644031830369309712267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28732203006190605970264181 2693644031830369309712267)
                      ·
                        rfl

theorem cell23_5245853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_5245853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5245853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5245853 prefixEnd_5245853 := by exact prefixLift 5245853
  have htrace : WordTrace (prefixWord ++ tailWord_5245853) baseStart_5245853 baseEnd_5245853 := by
    simpa [prefixWord, tailWord_5245853, baseEnd_5245853] using wordTrace_append hprefix tailTrace_5245853
  have hstable : (prefixWord ++ tailWord_5245853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5245853).length < 2 ^ (prefixWord ++ tailWord_5245853).sum := by decide
  have hdescent : baseEnd_5245853 < baseStart_5245853 := by decide
  rcases family_descends (prefixWord ++ tailWord_5245853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5245903 : List Nat := [1, 1, 2, 1, 1, 7, 1, 1, 1, 7]
def baseStart_5245903 : Nat := 118140960795 + 5245903 * 2 ^ 59
def prefixEnd_5245903 : Nat := 4983230072969 + 3 ^ 40 * 5245903 * 2
def baseEnd_5245903 : Nat := 897889901954364704695679

theorem tailTrace_5245903 : CollatzResearch.WordTrace tailWord_5245903 prefixEnd_5245903 897889901954364704695679 := by
  unfold tailWord_5245903
  simp only [CollatzResearch.WordTrace]
  refine ⟨191333801113996834748966363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127555867409331223165977575 191333801113996834748966363)
  ·
    refine ⟨287000701670995252123449545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191333801113996834748966363 287000701670995252123449545)
    ·
      refine ⟨215250526253246439092587159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287000701670995252123449545 215250526253246439092587159)
      ·
        refine ⟨322875789379869658638880739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215250526253246439092587159 322875789379869658638880739)
        ·
          refine ⟨484313684069804487958321109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322875789379869658638880739 484313684069804487958321109)
          ·
            refine ⟨11351101970386042686523151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 484313684069804487958321109 11351101970386042686523151)
            ·
              refine ⟨17026652955579064029784727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11351101970386042686523151 17026652955579064029784727)
              ·
                refine ⟨25539979433368596044677091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17026652955579064029784727 25539979433368596044677091)
                ·
                  refine ⟨38309969150052894067015637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25539979433368596044677091 38309969150052894067015637)
                  ·
                    refine ⟨897889901954364704695679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38309969150052894067015637 897889901954364704695679)
                    ·
                      rfl

theorem cell23_5245903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 7].length) (baseStart_5245903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5245903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5245903 prefixEnd_5245903 := by exact prefixLift 5245903
  have htrace : WordTrace (prefixWord ++ tailWord_5245903) baseStart_5245903 baseEnd_5245903 := by
    simpa [prefixWord, tailWord_5245903, baseEnd_5245903] using wordTrace_append hprefix tailTrace_5245903
  have hstable : (prefixWord ++ tailWord_5245903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5245903).length < 2 ^ (prefixWord ++ tailWord_5245903).sum := by decide
  have hdescent : baseEnd_5245903 < baseStart_5245903 := by decide
  rcases family_descends (prefixWord ++ tailWord_5245903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5245960 : List Nat := [2, 1, 3, 2, 1, 3, 2, 1, 1, 4, 3]
def baseStart_5245960 : Nat := 118140960795 + 5245960 * 2 ^ 59
def prefixEnd_5245960 : Nat := 4983230072969 + 3 ^ 40 * 5245960 * 2
def baseEnd_5245960 : Nat := 2693698974260400391074275

theorem tailTrace_5245960 : CollatzResearch.WordTrace tailWord_5245960 prefixEnd_5245960 2693698974260400391074275 := by
  unfold tailWord_5245960
  simp only [CollatzResearch.WordTrace]
  refine ⟨95667940037395166741895667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127557253383193555655860889 95667940037395166741895667)
  ·
    refine ⟨143501910056092750112843501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95667940037395166741895667 143501910056092750112843501)
    ·
      refine ⟨53813216271034781292316313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143501910056092750112843501 53813216271034781292316313)
      ·
        refine ⟨40359912203276085969237235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53813216271034781292316313 40359912203276085969237235)
        ·
          refine ⟨60539868304914128953855853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40359912203276085969237235 60539868304914128953855853)
          ·
            refine ⟨22702450614342798357695945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60539868304914128953855853 22702450614342798357695945)
            ·
              refine ⟨17026837960757098768271959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22702450614342798357695945 17026837960757098768271959)
              ·
                refine ⟨25540256941135648152407939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17026837960757098768271959 25540256941135648152407939)
                ·
                  refine ⟨38310385411703472228611909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25540256941135648152407939 38310385411703472228611909)
                  ·
                    refine ⟨7183197264694401042864733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38310385411703472228611909 7183197264694401042864733)
                    ·
                      refine ⟨2693698974260400391074275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7183197264694401042864733 2693698974260400391074275)
                      ·
                        rfl

theorem cell23_5245960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_5245960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5245960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5245960 prefixEnd_5245960 := by exact prefixLift 5245960
  have htrace : WordTrace (prefixWord ++ tailWord_5245960) baseStart_5245960 baseEnd_5245960 := by
    simpa [prefixWord, tailWord_5245960, baseEnd_5245960] using wordTrace_append hprefix tailTrace_5245960
  have hstable : (prefixWord ++ tailWord_5245960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5245960).length < 2 ^ (prefixWord ++ tailWord_5245960).sum := by decide
  have hdescent : baseEnd_5245960 < baseStart_5245960 := by decide
  rcases family_descends (prefixWord ++ tailWord_5245960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5245963 : List Nat := [1, 1, 1, 1, 6, 2, 1, 2, 8]
def baseStart_5245963 : Nat := 118140960795 + 5245963 * 2 ^ 59
def prefixEnd_5245963 : Nat := 4983230072969 + 3 ^ 40 * 5245963 * 2
def baseEnd_5245963 : Nat := 299300057189151542148529

theorem tailTrace_5245963 : CollatzResearch.WordTrace tailWord_5245963 prefixEnd_5245963 299300057189151542148529 := by
  unfold tailWord_5245963
  simp only [CollatzResearch.WordTrace]
  refine ⟨191335989493779464996150543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127557326329186309997433695 191335989493779464996150543)
  ·
    refine ⟨287003984240669197494225815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191335989493779464996150543 287003984240669197494225815)
    ·
      refine ⟨430505976361003796241338723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287003984240669197494225815 430505976361003796241338723)
      ·
        refine ⟨645758964541505694362008085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 430505976361003796241338723 645758964541505694362008085)
        ·
          refine ⟨30269951462883079423219129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 645758964541505694362008085 30269951462883079423219129)
          ·
            refine ⟨22702463597162309567414347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30269951462883079423219129 22702463597162309567414347)
            ·
              refine ⟨34053695395743464351121521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22702463597162309567414347 34053695395743464351121521)
              ·
                refine ⟨25540271546807598263341141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34053695395743464351121521 25540271546807598263341141)
                ·
                  refine ⟨299300057189151542148529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25540271546807598263341141 299300057189151542148529)
                  ·
                    rfl

theorem cell23_5245963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 8].length) (baseStart_5245963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5245963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5245963 prefixEnd_5245963 := by exact prefixLift 5245963
  have htrace : WordTrace (prefixWord ++ tailWord_5245963) baseStart_5245963 baseEnd_5245963 := by
    simpa [prefixWord, tailWord_5245963, baseEnd_5245963] using wordTrace_append hprefix tailTrace_5245963
  have hstable : (prefixWord ++ tailWord_5245963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5245963).length < 2 ^ (prefixWord ++ tailWord_5245963).sum := by decide
  have hdescent : baseEnd_5245963 < baseStart_5245963 := by decide
  rcases family_descends (prefixWord ++ tailWord_5245963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5246024 : List Nat := [2, 1, 3, 1, 1, 1, 4, 5, 1, 1, 3]
def baseStart_5246024 : Nat := 118140960795 + 5246024 * 2 ^ 59
def prefixEnd_5246024 : Nat := 4983230072969 + 3 ^ 40 * 5246024 * 2
def baseEnd_5246024 : Nat := 2693731837022288140673981

theorem tailTrace_5246024 : CollatzResearch.WordTrace tailWord_5246024 prefixEnd_5246024 2693731837022288140673981 := by
  unfold tailWord_5246024
  simp only [CollatzResearch.WordTrace]
  refine ⟨95669107173279236207060563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127558809564372314942747417 95669107173279236207060563)
  ·
    refine ⟨143503660759918854310590845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95669107173279236207060563 143503660759918854310590845)
    ·
      refine ⟨53813872784969570366471567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143503660759918854310590845 53813872784969570366471567)
      ·
        refine ⟨80720809177454355549707351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53813872784969570366471567 80720809177454355549707351)
        ·
          refine ⟨121081213766181533324561027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80720809177454355549707351 121081213766181533324561027)
          ·
            refine ⟨181621820649272299986841541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121081213766181533324561027 181621820649272299986841541)
            ·
              refine ⟨34054091371738556247532789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 181621820649272299986841541 34054091371738556247532789)
              ·
                refine ⟨3192571066100489648206199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34054091371738556247532789 3192571066100489648206199)
                ·
                  refine ⟨4788856599150734472309299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3192571066100489648206199 4788856599150734472309299)
                  ·
                    refine ⟨7183284898726101708463949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4788856599150734472309299 7183284898726101708463949)
                    ·
                      refine ⟨2693731837022288140673981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7183284898726101708463949 2693731837022288140673981)
                      ·
                        rfl

theorem cell23_5246024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 5, 1, 1, 3].length) (baseStart_5246024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5246024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5246024 prefixEnd_5246024 := by exact prefixLift 5246024
  have htrace : WordTrace (prefixWord ++ tailWord_5246024) baseStart_5246024 baseEnd_5246024 := by
    simpa [prefixWord, tailWord_5246024, baseEnd_5246024] using wordTrace_append hprefix tailTrace_5246024
  have hstable : (prefixWord ++ tailWord_5246024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5246024).length < 2 ^ (prefixWord ++ tailWord_5246024).sum := by decide
  have hdescent : baseEnd_5246024 < baseStart_5246024 := by decide
  rcases family_descends (prefixWord ++ tailWord_5246024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5246034 : List Nat := [3, 2, 2, 1, 3, 1, 2, 2, 2, 3, 2]
def baseStart_5246034 : Nat := 118140960795 + 5246034 * 2 ^ 59
def prefixEnd_5246034 : Nat := 4983230072969 + 3 ^ 40 * 5246034 * 2
def baseEnd_5246034 : Nat := 2693736971828833101548935

theorem tailTrace_5246034 : CollatzResearch.WordTrace tailWord_5246034 prefixEnd_5246034 2693736971828833101548935 := by
  unfold tailWord_5246034
  simp only [CollatzResearch.WordTrace]
  refine ⟨47834644769130561030496289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127559052717681496081323437 47834644769130561030496289)
  ·
    refine ⟨35875983576847920772872217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47834644769130561030496289 35875983576847920772872217)
    ·
      refine ⟨26906987682635940579654163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35875983576847920772872217 26906987682635940579654163)
      ·
        refine ⟨40360481523953910869481245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26906987682635940579654163 40360481523953910869481245)
        ·
          refine ⟨15135180571482716576055467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40360481523953910869481245 15135180571482716576055467)
          ·
            refine ⟨22702770857224074864083201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15135180571482716576055467 22702770857224074864083201)
            ·
              refine ⟨17027078142918056148062401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22702770857224074864083201 17027078142918056148062401)
              ·
                refine ⟨12770308607188542111046801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17027078142918056148062401 12770308607188542111046801)
                ·
                  refine ⟨9577731455391406583285101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12770308607188542111046801 9577731455391406583285101)
                  ·
                    refine ⟨3591649295771777468731913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9577731455391406583285101 3591649295771777468731913)
                    ·
                      refine ⟨2693736971828833101548935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3591649295771777468731913 2693736971828833101548935)
                      ·
                        rfl

theorem cell23_5246034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 2, 2, 3, 2].length) (baseStart_5246034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5246034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5246034 prefixEnd_5246034 := by exact prefixLift 5246034
  have htrace : WordTrace (prefixWord ++ tailWord_5246034) baseStart_5246034 baseEnd_5246034 := by
    simpa [prefixWord, tailWord_5246034, baseEnd_5246034] using wordTrace_append hprefix tailTrace_5246034
  have hstable : (prefixWord ++ tailWord_5246034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5246034).length < 2 ^ (prefixWord ++ tailWord_5246034).sum := by decide
  have hdescent : baseEnd_5246034 < baseStart_5246034 := by decide
  rcases family_descends (prefixWord ++ tailWord_5246034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5246057 : List Nat := [1, 2, 1, 1, 1, 6, 2, 3, 2, 4]
def baseStart_5246057 : Nat := 118140960795 + 5246057 * 2 ^ 59
def prefixEnd_5246057 : Nat := 4983230072969 + 3 ^ 40 * 5246057 * 2
def baseEnd_5246057 : Nat := 897916260627962170520443

theorem tailTrace_5246057 : CollatzResearch.WordTrace tailWord_5246057 prefixEnd_5246057 897916260627962170520443 := by
  unfold tailWord_5246057
  simp only [CollatzResearch.WordTrace]
  refine ⟨191339417955438919050072425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127559611970292612700048283 191339417955438919050072425)
  ·
    refine ⟨143504563466579189287554319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191339417955438919050072425 143504563466579189287554319)
    ·
      refine ⟨215256845199868783931331479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143504563466579189287554319 215256845199868783931331479)
      ·
        refine ⟨322885267799803175896997219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215256845199868783931331479 322885267799803175896997219)
        ·
          refine ⟨484327901699704763845495829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322885267799803175896997219 484327901699704763845495829)
          ·
            refine ⟨22702870392173660805257617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 484327901699704763845495829 22702870392173660805257617)
            ·
              refine ⟨17027152794130245603943213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22702870392173660805257617 17027152794130245603943213)
              ·
                refine ⟨6385182297798842101478705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17027152794130245603943213 6385182297798842101478705)
                ·
                  refine ⟨4788886723349131576109029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6385182297798842101478705 4788886723349131576109029)
                  ·
                    refine ⟨897916260627962170520443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4788886723349131576109029 897916260627962170520443)
                    ·
                      rfl

theorem cell23_5246057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 3, 2, 4].length) (baseStart_5246057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5246057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5246057 prefixEnd_5246057 := by exact prefixLift 5246057
  have htrace : WordTrace (prefixWord ++ tailWord_5246057) baseStart_5246057 baseEnd_5246057 := by
    simpa [prefixWord, tailWord_5246057, baseEnd_5246057] using wordTrace_append hprefix tailTrace_5246057
  have hstable : (prefixWord ++ tailWord_5246057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5246057).length < 2 ^ (prefixWord ++ tailWord_5246057).sum := by decide
  have hdescent : baseEnd_5246057 < baseStart_5246057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5246057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5246064 : List Nat := [2, 1, 1, 1, 5, 1, 3, 2, 3, 2, 2]
def baseStart_5246064 : Nat := 118140960795 + 5246064 * 2 ^ 59
def prefixEnd_5246064 : Nat := 4983230072969 + 3 ^ 40 * 5246064 * 2
def baseEnd_5246064 : Nat := 2693752376248467984173797

theorem tailTrace_5246064 : CollatzResearch.WordTrace tailWord_5246064 prefixEnd_5246064 2693752376248467984173797 := by
  unfold tailWord_5246064
  simp only [CollatzResearch.WordTrace]
  refine ⟨95669836633206779622788623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127559782177609039497051497 95669836633206779622788623)
  ·
    refine ⟨143504754949810169434182935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95669836633206779622788623 143504754949810169434182935)
    ·
      refine ⟨215257132424715254151274403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143504754949810169434182935 215257132424715254151274403)
      ·
        refine ⟨322885698637072881226911605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215257132424715254151274403 322885698637072881226911605)
        ·
          refine ⟨30270534247225582615022963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 322885698637072881226911605 30270534247225582615022963)
          ·
            refine ⟨45405801370838373922534445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30270534247225582615022963 45405801370838373922534445)
            ·
              refine ⟨17027175514064390220950417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45405801370838373922534445 17027175514064390220950417)
              ·
                refine ⟨12770381635548292665712813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17027175514064390220950417 12770381635548292665712813)
                ·
                  refine ⟨4788893113330609749642305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12770381635548292665712813 4788893113330609749642305)
                  ·
                    refine ⟨3591669834997957312231729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4788893113330609749642305 3591669834997957312231729)
                    ·
                      refine ⟨2693752376248467984173797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3591669834997957312231729 2693752376248467984173797)
                      ·
                        rfl

theorem cell23_5246064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 2, 3, 2, 2].length) (baseStart_5246064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5246064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5246064 prefixEnd_5246064 := by exact prefixLift 5246064
  have htrace : WordTrace (prefixWord ++ tailWord_5246064) baseStart_5246064 baseEnd_5246064 := by
    simpa [prefixWord, tailWord_5246064, baseEnd_5246064] using wordTrace_append hprefix tailTrace_5246064
  have hstable : (prefixWord ++ tailWord_5246064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5246064).length < 2 ^ (prefixWord ++ tailWord_5246064).sum := by decide
  have hdescent : baseEnd_5246064 < baseStart_5246064 := by decide
  rcases family_descends (prefixWord ++ tailWord_5246064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5246078 : List Nat := [4, 2, 4, 1, 1, 1, 1, 3, 1, 5]
def baseStart_5246078 : Nat := 118140960795 + 5246078 * 2 ^ 59
def prefixEnd_5246078 : Nat := 4983230072969 + 3 ^ 40 * 5246078 * 2
def baseEnd_5246078 : Nat := 897919854992543643132911

theorem tailTrace_5246078 : CollatzResearch.WordTrace tailWord_5246078 prefixEnd_5246078 897919854992543643132911 := by
  unfold tailWord_5246078
  simp only [CollatzResearch.WordTrace]
  refine ⟨23917522986045354954573361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127560122592241893091057925 23917522986045354954573361)
  ·
    refine ⟨17938142239534016215930021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23917522986045354954573361 17938142239534016215930021)
    ·
      refine ⟨3363401669912628040486879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17938142239534016215930021 3363401669912628040486879)
      ·
        refine ⟨5045102504868942060730319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3363401669912628040486879 5045102504868942060730319)
        ·
          refine ⟨7567653757303413091095479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5045102504868942060730319 7567653757303413091095479)
          ·
            refine ⟨11351480635955119636643219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7567653757303413091095479 11351480635955119636643219)
            ·
              refine ⟨17027220953932679454964829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11351480635955119636643219 17027220953932679454964829)
              ·
                refine ⟨6385207857724754795611811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17027220953932679454964829 6385207857724754795611811)
                ·
                  refine ⟨9577811786587132193417717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6385207857724754795611811 9577811786587132193417717)
                  ·
                    refine ⟨897919854992543643132911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9577811786587132193417717 897919854992543643132911)
                    ·
                      rfl

theorem cell23_5246078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_5246078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5246078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5246078 prefixEnd_5246078 := by exact prefixLift 5246078
  have htrace : WordTrace (prefixWord ++ tailWord_5246078) baseStart_5246078 baseEnd_5246078 := by
    simpa [prefixWord, tailWord_5246078, baseEnd_5246078] using wordTrace_append hprefix tailTrace_5246078
  have hstable : (prefixWord ++ tailWord_5246078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5246078).length < 2 ^ (prefixWord ++ tailWord_5246078).sum := by decide
  have hdescent : baseEnd_5246078 < baseStart_5246078 := by decide
  rcases family_descends (prefixWord ++ tailWord_5246078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5246081 : List Nat := [1, 2, 4, 2, 2, 3, 2, 1, 1, 1, 4]
def baseStart_5246081 : Nat := 118140960795 + 5246081 * 2 ^ 59
def prefixEnd_5246081 : Nat := 4983230072969 + 3 ^ 40 * 5246081 * 2
def baseEnd_5246081 : Nat := 2693761105419594417661219

theorem tailTrace_5246081 : CollatzResearch.WordTrace tailWord_5246081 prefixEnd_5246081 2693761105419594417661219 := by
  unfold tailWord_5246081
  simp only [CollatzResearch.WordTrace]
  refine ⟨191340293307351971148946097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127560195538234647432630731 191340293307351971148946097)
  ·
    refine ⟨143505219980513978361709573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191340293307351971148946097 143505219980513978361709573)
    ·
      refine ⟨26907228746346370942820545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 143505219980513978361709573 26907228746346370942820545)
      ·
        refine ⟨20180421559759778207115409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26907228746346370942820545 20180421559759778207115409)
        ·
          refine ⟨15135316169819833655336557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20180421559759778207115409 15135316169819833655336557)
          ·
            refine ⟨5675743563682437620751209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15135316169819833655336557 5675743563682437620751209)
            ·
              refine ⟨4256807672761828215563407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5675743563682437620751209 4256807672761828215563407)
              ·
                refine ⟨6385211509142742323345111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4256807672761828215563407 6385211509142742323345111)
                ·
                  refine ⟨9577817263714113485017667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6385211509142742323345111 9577817263714113485017667)
                  ·
                    refine ⟨14366725895571170227526501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9577817263714113485017667 14366725895571170227526501)
                    ·
                      refine ⟨2693761105419594417661219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14366725895571170227526501 2693761105419594417661219)
                      ·
                        rfl

theorem cell23_5246081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_5246081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5246081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5246081 prefixEnd_5246081 := by exact prefixLift 5246081
  have htrace : WordTrace (prefixWord ++ tailWord_5246081) baseStart_5246081 baseEnd_5246081 := by
    simpa [prefixWord, tailWord_5246081, baseEnd_5246081] using wordTrace_append hprefix tailTrace_5246081
  have hstable : (prefixWord ++ tailWord_5246081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5246081).length < 2 ^ (prefixWord ++ tailWord_5246081).sum := by decide
  have hdescent : baseEnd_5246081 < baseStart_5246081 := by decide
  rcases family_descends (prefixWord ++ tailWord_5246081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5246084 : List Nat := [2, 3, 2, 1, 2, 3, 1, 3, 1, 2, 3]
def baseStart_5246084 : Nat := 118140960795 + 5246084 * 2 ^ 59
def prefixEnd_5246084 : Nat := 4983230072969 + 3 ^ 40 * 5246084 * 2
def baseEnd_5246084 : Nat := 2693762645861557905923705

theorem tailTrace_5246084 : CollatzResearch.WordTrace tailWord_5246084 prefixEnd_5246084 2693762645861557905923705 := by
  unfold tailWord_5246084
  simp only [CollatzResearch.WordTrace]
  refine ⟨95670201363170551330652653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127560268484227401774203537 95670201363170551330652653)
  ·
    refine ⟨35876325511188956748994745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95670201363170551330652653 35876325511188956748994745)
    ·
      refine ⟨26907244133391717561746059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35876325511188956748994745 26907244133391717561746059)
      ·
        refine ⟨40360866200087576342619089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26907244133391717561746059 40360866200087576342619089)
        ·
          refine ⟨30270649650065682256964317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40360866200087576342619089 30270649650065682256964317)
          ·
            refine ⟨11351493618774630846361619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30270649650065682256964317 11351493618774630846361619)
            ·
              refine ⟨17027240428161946269542429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11351493618774630846361619 17027240428161946269542429)
              ·
                refine ⟨6385215160560729851078411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17027240428161946269542429 6385215160560729851078411)
                ·
                  refine ⟨9577822740841094776617617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6385215160560729851078411 9577822740841094776617617)
                  ·
                    refine ⟨7183367055630821082463213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9577822740841094776617617 7183367055630821082463213)
                    ·
                      refine ⟨2693762645861557905923705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7183367055630821082463213 2693762645861557905923705)
                      ·
                        rfl

theorem cell23_5246084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 3, 1, 2, 3].length) (baseStart_5246084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5246084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5246084 prefixEnd_5246084 := by exact prefixLift 5246084
  have htrace : WordTrace (prefixWord ++ tailWord_5246084) baseStart_5246084 baseEnd_5246084 := by
    simpa [prefixWord, tailWord_5246084, baseEnd_5246084] using wordTrace_append hprefix tailTrace_5246084
  have hstable : (prefixWord ++ tailWord_5246084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5246084).length < 2 ^ (prefixWord ++ tailWord_5246084).sum := by decide
  have hdescent : baseEnd_5246084 < baseStart_5246084 := by decide
  rcases family_descends (prefixWord ++ tailWord_5246084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5246098 : List Nat := [3, 2, 3, 1, 1, 2, 2, 4, 1, 2, 2]
def baseStart_5246098 : Nat := 118140960795 + 5246098 * 2 ^ 59
def prefixEnd_5246098 : Nat := 4983230072969 + 3 ^ 40 * 5246098 * 2
def baseEnd_5246098 : Nat := 2693769834590720851148641

theorem tailTrace_5246098 : CollatzResearch.WordTrace tailWord_5246098 prefixEnd_5246098 2693769834590720851148641 := by
  unfold tailWord_5246098
  simp only [CollatzResearch.WordTrace]
  refine ⟨47835228337072595763078737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127560608898860255368209965 47835228337072595763078737)
  ·
    refine ⟨35876421252804446822309053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47835228337072595763078737 35876421252804446822309053)
    ·
      refine ⟨13453657969801667558365895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35876421252804446822309053 13453657969801667558365895)
      ·
        refine ⟨20180486954702501337548843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13453657969801667558365895 20180486954702501337548843)
        ·
          refine ⟨30270730432053752006323265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20180486954702501337548843 30270730432053752006323265)
          ·
            refine ⟨22703047824040314004742449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30270730432053752006323265 22703047824040314004742449)
            ·
              refine ⟨17027285868030235503556837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22703047824040314004742449 17027285868030235503556837)
              ·
                refine ⟨3192616100255669156916907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17027285868030235503556837 3192616100255669156916907)
                ·
                  refine ⟨4788924150383503735375361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3192616100255669156916907 4788924150383503735375361)
                  ·
                    refine ⟨3591693112787627801531521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4788924150383503735375361 3591693112787627801531521)
                    ·
                      refine ⟨2693769834590720851148641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3591693112787627801531521 2693769834590720851148641)
                      ·
                        rfl

theorem cell23_5246098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 4, 1, 2, 2].length) (baseStart_5246098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5246098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5246098 prefixEnd_5246098 := by exact prefixLift 5246098
  have htrace : WordTrace (prefixWord ++ tailWord_5246098) baseStart_5246098 baseEnd_5246098 := by
    simpa [prefixWord, tailWord_5246098, baseEnd_5246098] using wordTrace_append hprefix tailTrace_5246098
  have hstable : (prefixWord ++ tailWord_5246098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5246098).length < 2 ^ (prefixWord ++ tailWord_5246098).sum := by decide
  have hdescent : baseEnd_5246098 < baseStart_5246098 := by decide
  rcases family_descends (prefixWord ++ tailWord_5246098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5246111 : List Nat := [1, 1, 2, 6, 3, 1, 1, 1, 1, 2, 4]
def baseStart_5246111 : Nat := 118140960795 + 5246111 * 2 ^ 59
def prefixEnd_5246111 : Nat := 4983230072969 + 3 ^ 40 * 5246111 * 2
def baseEnd_5246111 : Nat := 2693776509839229300286081

theorem tailTrace_5246111 : CollatzResearch.WordTrace tailWord_5246111 prefixEnd_5246111 2693776509839229300286081 := by
  unfold tailWord_5246111
  simp only [CollatzResearch.WordTrace]
  refine ⟨191341387497243286272538187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127560924998162190848358791 191341387497243286272538187)
  ·
    refine ⟨287012081245864929408807281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191341387497243286272538187 287012081245864929408807281)
    ·
      refine ⟨215259060934398697056605461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287012081245864929408807281 215259060934398697056605461)
      ·
        refine ⟨10090268481299938924528381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 215259060934398697056605461 10090268481299938924528381)
        ·
          refine ⟨3783850680487477096698143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10090268481299938924528381 3783850680487477096698143)
          ·
            refine ⟨5675776020731215645047215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3783850680487477096698143 5675776020731215645047215)
            ·
              refine ⟨8513664031096823467570823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5675776020731215645047215 8513664031096823467570823)
              ·
                refine ⟨12770496046645235201356235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8513664031096823467570823 12770496046645235201356235)
                ·
                  refine ⟨19155744069967852802034353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12770496046645235201356235 19155744069967852802034353)
                  ·
                    refine ⟨14366808052475889601525765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19155744069967852802034353 14366808052475889601525765)
                    ·
                      refine ⟨2693776509839229300286081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14366808052475889601525765 2693776509839229300286081)
                      ·
                        rfl

theorem cell23_5246111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_5246111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5246111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5246111 prefixEnd_5246111 := by exact prefixLift 5246111
  have htrace : WordTrace (prefixWord ++ tailWord_5246111) baseStart_5246111 baseEnd_5246111 := by
    simpa [prefixWord, tailWord_5246111, baseEnd_5246111] using wordTrace_append hprefix tailTrace_5246111
  have hstable : (prefixWord ++ tailWord_5246111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5246111).length < 2 ^ (prefixWord ++ tailWord_5246111).sum := by decide
  have hdescent : baseEnd_5246111 < baseStart_5246111 := by decide
  rcases family_descends (prefixWord ++ tailWord_5246111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5246207 : List Nat := [1, 1, 2, 2, 1, 5, 2, 2, 2, 5]
def baseStart_5246207 : Nat := 118140960795 + 5246207 * 2 ^ 59
def prefixEnd_5246207 : Nat := 4983230072969 + 3 ^ 40 * 5246207 * 2
def baseEnd_5246207 : Nat := 897941934660686974895213

theorem tailTrace_5246207 : CollatzResearch.WordTrace tailWord_5246207 prefixEnd_5246207 897941934660686974895213 := by
  unfold tailWord_5246207
  simp only [CollatzResearch.WordTrace]
  refine ⟨191344888904895494668032875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127563259269930329778688583 191344888904895494668032875)
  ·
    refine ⟨287017333357343242002049313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191344888904895494668032875 287017333357343242002049313)
    ·
      refine ⟨215263000018007431501536985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287017333357343242002049313 215263000018007431501536985)
      ·
        refine ⟨161447250013505573626152739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215263000018007431501536985 161447250013505573626152739)
        ·
          refine ⟨242170875020258360439229109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161447250013505573626152739 242170875020258360439229109)
          ·
            refine ⟨22703519533149221291177729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 242170875020258360439229109 22703519533149221291177729)
            ·
              refine ⟨17027639649861915968383297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22703519533149221291177729 17027639649861915968383297)
              ·
                refine ⟨12770729737396436976287473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17027639649861915968383297 12770729737396436976287473)
                ·
                  refine ⟨9578047303047327732215605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12770729737396436976287473 9578047303047327732215605)
                  ·
                    refine ⟨897941934660686974895213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9578047303047327732215605 897941934660686974895213)
                    ·
                      rfl

theorem cell23_5246207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 2, 2, 5].length) (baseStart_5246207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5246207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5246207 prefixEnd_5246207 := by exact prefixLift 5246207
  have htrace : WordTrace (prefixWord ++ tailWord_5246207) baseStart_5246207 baseEnd_5246207 := by
    simpa [prefixWord, tailWord_5246207, baseEnd_5246207] using wordTrace_append hprefix tailTrace_5246207
  have hstable : (prefixWord ++ tailWord_5246207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5246207).length < 2 ^ (prefixWord ++ tailWord_5246207).sum := by decide
  have hdescent : baseEnd_5246207 < baseStart_5246207 := by decide
  rcases family_descends (prefixWord ++ tailWord_5246207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5246211 : List Nat := [1, 1, 1, 3, 2, 6, 2, 2, 5]
def baseStart_5246211 : Nat := 118140960795 + 5246211 * 2 ^ 59
def prefixEnd_5246211 : Nat := 4983230072969 + 3 ^ 40 * 5246211 * 2
def baseEnd_5246211 : Nat := 299314206433853212115069

theorem tailTrace_5246211 : CollatzResearch.WordTrace tailWord_5246211 prefixEnd_5246211 299314206433853212115069 := by
  unfold tailWord_5246211
  simp only [CollatzResearch.WordTrace]
  refine ⟨191345034796881003351178487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127563356531254002234118991 191345034796881003351178487)
  ·
    refine ⟨287017552195321505026767731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191345034796881003351178487 287017552195321505026767731)
    ·
      refine ⟨430526328292982257540151597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287017552195321505026767731 430526328292982257540151597)
      ·
        refine ⟨161447373109868346577556849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 430526328292982257540151597 161447373109868346577556849)
        ·
          refine ⟨121085529832401259933167637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161447373109868346577556849 121085529832401259933167637)
          ·
            refine ⟨5675884210893809059367233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 121085529832401259933167637 5675884210893809059367233)
            ·
              refine ⟨4256913158170356794525425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5675884210893809059367233 4256913158170356794525425)
              ·
                refine ⟨3192684868627767595894069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4256913158170356794525425 3192684868627767595894069)
                ·
                  refine ⟨299314206433853212115069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3192684868627767595894069 299314206433853212115069)
                  ·
                    rfl

theorem cell23_5246211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 2, 2, 5].length) (baseStart_5246211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5246211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5246211 prefixEnd_5246211 := by exact prefixLift 5246211
  have htrace : WordTrace (prefixWord ++ tailWord_5246211) baseStart_5246211 baseEnd_5246211 := by
    simpa [prefixWord, tailWord_5246211, baseEnd_5246211] using wordTrace_append hprefix tailTrace_5246211
  have hstable : (prefixWord ++ tailWord_5246211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5246211).length < 2 ^ (prefixWord ++ tailWord_5246211).sum := by decide
  have hdescent : baseEnd_5246211 < baseStart_5246211 := by decide
  rcases family_descends (prefixWord ++ tailWord_5246211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5246244 : List Nat := [2, 3, 1, 3, 1, 1, 1, 2, 1, 6, 2]
def baseStart_5246244 : Nat := 118140960795 + 5246244 * 2 ^ 59
def prefixEnd_5246244 : Nat := 4983230072969 + 3 ^ 40 * 5246244 * 2
def baseEnd_5246244 : Nat := 2693844802766277279922969

theorem tailTrace_5246244 : CollatzResearch.WordTrace tailWord_5246244 prefixEnd_5246244 2693844802766277279922969 := by
  unfold tailWord_5246244
  simp only [CollatzResearch.WordTrace]
  refine ⟨95673119202880724993564893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127564158937174299991419857 95673119202880724993564893)
  ·
    refine ⟨35877419701080271872586835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95673119202880724993564893 35877419701080271872586835)
    ·
      refine ⟨53816129551620407808880253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35877419701080271872586835 53816129551620407808880253)
      ·
        refine ⟨20181048581857652928330095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53816129551620407808880253 20181048581857652928330095)
        ·
          refine ⟨30271572872786479392495143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20181048581857652928330095 30271572872786479392495143)
          ·
            refine ⟨45407359309179719088742715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30271572872786479392495143 45407359309179719088742715)
            ·
              refine ⟨68111038963769578633114073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45407359309179719088742715 68111038963769578633114073)
              ·
                refine ⟨51083279222827183974835555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68111038963769578633114073 51083279222827183974835555)
                ·
                  refine ⟨76624918834240775962253333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51083279222827183974835555 76624918834240775962253333)
                  ·
                    refine ⟨3591793070355036373230625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 76624918834240775962253333 3591793070355036373230625)
                    ·
                      refine ⟨2693844802766277279922969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3591793070355036373230625 2693844802766277279922969)
                      ·
                        rfl

theorem cell23_5246244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_5246244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5246244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5246244 prefixEnd_5246244 := by exact prefixLift 5246244
  have htrace : WordTrace (prefixWord ++ tailWord_5246244) baseStart_5246244 baseEnd_5246244 := by
    simpa [prefixWord, tailWord_5246244, baseEnd_5246244] using wordTrace_append hprefix tailTrace_5246244
  have hstable : (prefixWord ++ tailWord_5246244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5246244).length < 2 ^ (prefixWord ++ tailWord_5246244).sum := by decide
  have hdescent : baseEnd_5246244 < baseStart_5246244 := by decide
  rcases family_descends (prefixWord ++ tailWord_5246244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5246257 : List Nat := [1, 2, 2, 3, 3, 1, 1, 1, 2, 1, 6]
def baseStart_5246257 : Nat := 118140960795 + 5246257 * 2 ^ 59
def prefixEnd_5246257 : Nat := 4983230072969 + 3 ^ 40 * 5246257 * 2
def baseEnd_5246257 : Nat := 2693851478014785729060409

theorem tailTrace_5246257 : CollatzResearch.WordTrace tailWord_5246257 prefixEnd_5246257 2693851478014785729060409 := by
  unfold tailWord_5246257
  simp only [CollatzResearch.WordTrace]
  refine ⟨191346712554714353207353025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127564475036476235471568683 191346712554714353207353025)
  ·
    refine ⟨143510034416035764905514769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191346712554714353207353025 143510034416035764905514769)
    ·
      refine ⟨107632525812026823679136077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143510034416035764905514769 107632525812026823679136077)
      ·
        refine ⟨40362197179510058879676029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107632525812026823679136077 40362197179510058879676029)
        ·
          refine ⟨15135823942316272079878511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40362197179510058879676029 15135823942316272079878511)
          ·
            refine ⟨22703735913474408119817767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15135823942316272079878511 22703735913474408119817767)
            ·
              refine ⟨34055603870211612179726651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22703735913474408119817767 34055603870211612179726651)
              ·
                refine ⟨51083405805317418269589977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34055603870211612179726651 51083405805317418269589977)
                ·
                  refine ⟨38312554353988063702192483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51083405805317418269589977 38312554353988063702192483)
                  ·
                    refine ⟨57468831530982095553288725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38312554353988063702192483 57468831530982095553288725)
                    ·
                      refine ⟨2693851478014785729060409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57468831530982095553288725 2693851478014785729060409)
                      ·
                        rfl

theorem cell23_5246257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_5246257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5246257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5246257 prefixEnd_5246257 := by exact prefixLift 5246257
  have htrace : WordTrace (prefixWord ++ tailWord_5246257) baseStart_5246257 baseEnd_5246257 := by
    simpa [prefixWord, tailWord_5246257, baseEnd_5246257] using wordTrace_append hprefix tailTrace_5246257
  have hstable : (prefixWord ++ tailWord_5246257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5246257).length < 2 ^ (prefixWord ++ tailWord_5246257).sum := by decide
  have hdescent : baseEnd_5246257 < baseStart_5246257 := by decide
  rcases family_descends (prefixWord ++ tailWord_5246257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5246271 : List Nat := [1, 1, 2, 2, 4, 2, 2, 4, 1, 4]
def baseStart_5246271 : Nat := 118140960795 + 5246271 * 2 ^ 59
def prefixEnd_5246271 : Nat := 4983230072969 + 3 ^ 40 * 5246271 * 2
def baseEnd_5246271 : Nat := 897952888914649558095115

theorem tailTrace_5246271 : CollatzResearch.WordTrace tailWord_5246271 prefixEnd_5246271 897952888914649558095115 := by
  unfold tailWord_5246271
  simp only [CollatzResearch.WordTrace]
  refine ⟨191347223176663633598362667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127564815451109089065575111 191347223176663633598362667)
  ·
    refine ⟨287020834764995450397544001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191347223176663633598362667 287020834764995450397544001)
    ·
      refine ⟨215265626073746587798158001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287020834764995450397544001 215265626073746587798158001)
      ·
        refine ⟨161449219555309940848618501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215265626073746587798158001 161449219555309940848618501)
        ·
          refine ⟨30271728666620613909115969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 161449219555309940848618501 30271728666620613909115969)
          ·
            refine ⟨22703796499965460431836977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30271728666620613909115969 22703796499965460431836977)
            ·
              refine ⟨17027847374974095323877733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22703796499965460431836977 17027847374974095323877733)
              ·
                refine ⟨3192721382807642873227075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17027847374974095323877733 3192721382807642873227075)
                ·
                  refine ⟨4789082074211464309840613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3192721382807642873227075 4789082074211464309840613)
                  ·
                    refine ⟨897952888914649558095115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4789082074211464309840613 897952888914649558095115)
                    ·
                      rfl

theorem cell23_5246271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 4, 1, 4].length) (baseStart_5246271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5246271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5246271 prefixEnd_5246271 := by exact prefixLift 5246271
  have htrace : WordTrace (prefixWord ++ tailWord_5246271) baseStart_5246271 baseEnd_5246271 := by
    simpa [prefixWord, tailWord_5246271, baseEnd_5246271] using wordTrace_append hprefix tailTrace_5246271
  have hstable : (prefixWord ++ tailWord_5246271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5246271).length < 2 ^ (prefixWord ++ tailWord_5246271).sum := by decide
  have hdescent : baseEnd_5246271 < baseStart_5246271 := by decide
  rcases family_descends (prefixWord ++ tailWord_5246271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5246297 : List Nat := [1, 2, 1, 2, 2, 2, 2, 3, 3, 5]
def baseStart_5246297 : Nat := 118140960795 + 5246297 * 2 ^ 59
def prefixEnd_5246297 : Nat := 4983230072969 + 3 ^ 40 * 5246297 * 2
def baseEnd_5246297 : Nat := 897957339080321857520075

theorem tailTrace_5246297 : CollatzResearch.WordTrace tailWord_5246297 prefixEnd_5246297 897957339080321857520075 := by
  unfold tailWord_5246297
  simp only [CollatzResearch.WordTrace]
  refine ⟨191348171474569440038809145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127565447649712960025872763 191348171474569440038809145)
  ·
    refine ⟨143511128605927080029106859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191348171474569440038809145 143511128605927080029106859)
    ·
      refine ⟨215266692908890620043660289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143511128605927080029106859 215266692908890620043660289)
      ·
        refine ⟨161450019681667965032745217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215266692908890620043660289 161450019681667965032745217)
        ·
          refine ⟨121087514761250973774558913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161450019681667965032745217 121087514761250973774558913)
          ·
            refine ⟨90815636070938230330919185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121087514761250973774558913 90815636070938230330919185)
            ·
              refine ⟨68111727053203672748189389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90815636070938230330919185 68111727053203672748189389)
              ·
                refine ⟨25541897644951377280571021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68111727053203672748189389 25541897644951377280571021)
                ·
                  refine ⟨9578211616856766480214133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25541897644951377280571021 9578211616856766480214133)
                  ·
                    refine ⟨897957339080321857520075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9578211616856766480214133 897957339080321857520075)
                    ·
                      rfl

theorem cell23_5246297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 3, 5].length) (baseStart_5246297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5246297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5246297 prefixEnd_5246297 := by exact prefixLift 5246297
  have htrace : WordTrace (prefixWord ++ tailWord_5246297) baseStart_5246297 baseEnd_5246297 := by
    simpa [prefixWord, tailWord_5246297, baseEnd_5246297] using wordTrace_append hprefix tailTrace_5246297
  have hstable : (prefixWord ++ tailWord_5246297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5246297).length < 2 ^ (prefixWord ++ tailWord_5246297).sum := by decide
  have hdescent : baseEnd_5246297 < baseStart_5246297 := by decide
  rcases family_descends (prefixWord ++ tailWord_5246297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5246347 : List Nat := [1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 6]
def baseStart_5246347 : Nat := 118140960795 + 5246347 * 2 ^ 59
def prefixEnd_5246347 : Nat := 4983230072969 + 3 ^ 40 * 5246347 * 2
def baseEnd_5246347 : Nat := 2693897691273690376934995

theorem tailTrace_5246347 : CollatzResearch.WordTrace tailWord_5246347 prefixEnd_5246347 2693897691273690376934995 := by
  unfold tailWord_5246347
  simp only [CollatzResearch.WordTrace]
  refine ⟨191349995124388298578129295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127566663416258865718752863 191349995124388298578129295)
  ·
    refine ⟨287024992686582447867193943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191349995124388298578129295 287024992686582447867193943)
    ·
      refine ⟨430537489029873671800790915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287024992686582447867193943 430537489029873671800790915)
      ·
        refine ⟨645806233544810507701186373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 430537489029873671800790915 645806233544810507701186373)
        ·
          refine ⟨121088668789651970193972445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 645806233544810507701186373 121088668789651970193972445)
          ·
            refine ⟨45408250796119488822739667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121088668789651970193972445 45408250796119488822739667)
            ·
              refine ⟨68112376194179233234109501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45408250796119488822739667 68112376194179233234109501)
              ·
                refine ⟨25542141072817212462791063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68112376194179233234109501 25542141072817212462791063)
                ·
                  refine ⟨38313211609225818694186595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25542141072817212462791063 38313211609225818694186595)
                  ·
                    refine ⟨57469817413838728041279893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38313211609225818694186595 57469817413838728041279893)
                    ·
                      refine ⟨2693897691273690376934995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57469817413838728041279893 2693897691273690376934995)
                      ·
                        rfl

theorem cell23_5246347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 6].length) (baseStart_5246347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5246347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5246347 prefixEnd_5246347 := by exact prefixLift 5246347
  have htrace : WordTrace (prefixWord ++ tailWord_5246347) baseStart_5246347 baseEnd_5246347 := by
    simpa [prefixWord, tailWord_5246347, baseEnd_5246347] using wordTrace_append hprefix tailTrace_5246347
  have hstable : (prefixWord ++ tailWord_5246347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5246347).length < 2 ^ (prefixWord ++ tailWord_5246347).sum := by decide
  have hdescent : baseEnd_5246347 < baseStart_5246347 := by decide
  rcases family_descends (prefixWord ++ tailWord_5246347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5246357 : List Nat := [1, 3, 2, 1, 1, 2, 4, 9]
def baseStart_5246357 : Nat := 118140960795 + 5246357 * 2 ^ 59
def prefixEnd_5246357 : Nat := 4983230072969 + 3 ^ 40 * 5246357 * 2
def baseEnd_5246357 : Nat := 99774178743712419918887

theorem tailTrace_5246357 : CollatzResearch.WordTrace tailWord_5246357 prefixEnd_5246357 99774178743712419918887 := by
  unfold tailWord_5246357
  simp only [CollatzResearch.WordTrace]
  refine ⟨191350359854352070285993325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127566906569568046857328883 191350359854352070285993325)
  ·
    refine ⟨71756384945382026357247497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191350359854352070285993325 71756384945382026357247497)
    ·
      refine ⟨53817288709036519767935623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71756384945382026357247497 53817288709036519767935623)
      ·
        refine ⟨80725933063554779651903435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53817288709036519767935623 80725933063554779651903435)
        ·
          refine ⟨121088899595332169477855153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80725933063554779651903435 121088899595332169477855153)
          ·
            refine ⟨90816674696499127108391365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121088899595332169477855153 90816674696499127108391365)
            ·
              refine ⟨17028126505593586332823381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90816674696499127108391365 17028126505593586332823381)
              ·
                refine ⟨99774178743712419918887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17028126505593586332823381 99774178743712419918887)
                ·
                  rfl

theorem cell23_5246357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 9].length) (baseStart_5246357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5246357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5246357 prefixEnd_5246357 := by exact prefixLift 5246357
  have htrace : WordTrace (prefixWord ++ tailWord_5246357) baseStart_5246357 baseEnd_5246357 := by
    simpa [prefixWord, tailWord_5246357, baseEnd_5246357] using wordTrace_append hprefix tailTrace_5246357
  have hstable : (prefixWord ++ tailWord_5246357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5246357).length < 2 ^ (prefixWord ++ tailWord_5246357).sum := by decide
  have hdescent : baseEnd_5246357 < baseStart_5246357 := by decide
  rcases family_descends (prefixWord ++ tailWord_5246357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5246385 : List Nat := [1, 2, 2, 4, 1, 1, 3, 4, 1, 2, 2]
def baseStart_5246385 : Nat := 118140960795 + 5246385 * 2 ^ 59
def prefixEnd_5246385 : Nat := 4983230072969 + 3 ^ 40 * 5246385 * 2
def baseEnd_5246385 : Nat := 2693917203538561228259821

theorem tailTrace_5246385 : CollatzResearch.WordTrace tailWord_5246385 prefixEnd_5246385 2693917203538561228259821 := by
  unfold tailWord_5246385
  simp only [CollatzResearch.WordTrace]
  refine ⟨191351381098250631068012609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127567587398833754045341739 191351381098250631068012609)
  ·
    refine ⟨143513535823687973301009457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191351381098250631068012609 143513535823687973301009457)
    ·
      refine ⟨107635151867765979975757093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143513535823687973301009457 107635151867765979975757093)
      ·
        refine ⟨20181590975206121245454455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107635151867765979975757093 20181590975206121245454455)
        ·
          refine ⟨30272386462809181868181683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20181590975206121245454455 30272386462809181868181683)
          ·
            refine ⟨45408579694213772802272525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30272386462809181868181683 45408579694213772802272525)
            ·
              refine ⟨17028217385330164800852197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45408579694213772802272525 17028217385330164800852197)
              ·
                refine ⟨3192790759749405900159787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17028217385330164800852197 3192790759749405900159787)
                ·
                  refine ⟨4789186139624108850239681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3192790759749405900159787 4789186139624108850239681)
                  ·
                    refine ⟨3591889604718081637679761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4789186139624108850239681 3591889604718081637679761)
                    ·
                      refine ⟨2693917203538561228259821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3591889604718081637679761 2693917203538561228259821)
                      ·
                        rfl

theorem cell23_5246385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 4, 1, 2, 2].length) (baseStart_5246385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5246385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5246385 prefixEnd_5246385 := by exact prefixLift 5246385
  have htrace : WordTrace (prefixWord ++ tailWord_5246385) baseStart_5246385 baseEnd_5246385 := by
    simpa [prefixWord, tailWord_5246385, baseEnd_5246385] using wordTrace_append hprefix tailTrace_5246385
  have hstable : (prefixWord ++ tailWord_5246385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5246385).length < 2 ^ (prefixWord ++ tailWord_5246385).sum := by decide
  have hdescent : baseEnd_5246385 < baseStart_5246385 := by decide
  rcases family_descends (prefixWord ++ tailWord_5246385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5246411 : List Nat := [1, 1, 1, 1, 3, 3, 4, 1, 3, 3, 2]
def baseStart_5246411 : Nat := 118140960795 + 5246411 * 2 ^ 59
def prefixEnd_5246411 : Nat := 4983230072969 + 3 ^ 40 * 5246411 * 2
def baseEnd_5246411 : Nat := 2693930554035578126534701

theorem tailTrace_5246411 : CollatzResearch.WordTrace tailWord_5246411 prefixEnd_5246411 2693930554035578126534701 := by
  unfold tailWord_5246411
  simp only [CollatzResearch.WordTrace]
  refine ⟨191352329396156437508459087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127568219597437625005639391 191352329396156437508459087)
  ·
    refine ⟨287028494094234656262688631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191352329396156437508459087 287028494094234656262688631)
    ·
      refine ⟨430542741141351984394032947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287028494094234656262688631 430542741141351984394032947)
      ·
        refine ⟨645814111712027976591049421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 430542741141351984394032947 645814111712027976591049421)
        ·
          refine ⟨242180291892010491221643533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 645814111712027976591049421 242180291892010491221643533)
          ·
            refine ⟨90817609459503934208116325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 242180291892010491221643533 90817609459503934208116325)
            ·
              refine ⟨17028301773656987664021811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90817609459503934208116325 17028301773656987664021811)
              ·
                refine ⟨25542452660485481496032717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17028301773656987664021811 25542452660485481496032717)
                ·
                  refine ⟨9578419747682055561012269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25542452660485481496032717 9578419747682055561012269)
                  ·
                    refine ⟨3591907405380770835379601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9578419747682055561012269 3591907405380770835379601)
                    ·
                      refine ⟨2693930554035578126534701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3591907405380770835379601 2693930554035578126534701)
                      ·
                        rfl

theorem cell23_5246411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 3, 3, 2].length) (baseStart_5246411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5246411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5246411 prefixEnd_5246411 := by exact prefixLift 5246411
  have htrace : WordTrace (prefixWord ++ tailWord_5246411) baseStart_5246411 baseEnd_5246411 := by
    simpa [prefixWord, tailWord_5246411, baseEnd_5246411] using wordTrace_append hprefix tailTrace_5246411
  have hstable : (prefixWord ++ tailWord_5246411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5246411).length < 2 ^ (prefixWord ++ tailWord_5246411).sum := by decide
  have hdescent : baseEnd_5246411 < baseStart_5246411 := by decide
  rcases family_descends (prefixWord ++ tailWord_5246411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5246422 : List Nat := [5, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3]
def baseStart_5246422 : Nat := 118140960795 + 5246422 * 2 ^ 59
def prefixEnd_5246422 : Nat := 4983230072969 + 3 ^ 40 * 5246422 * 2
def baseEnd_5246422 : Nat := 2693936202322777583497151

theorem tailTrace_5246422 : CollatzResearch.WordTrace tailWord_5246422 prefixEnd_5246422 2693936202322777583497151 := by
  unfold tailWord_5246422
  simp only [CollatzResearch.WordTrace]
  refine ⟨11959545662444786649194345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 127568487066077724258073013 11959545662444786649194345)
  ·
    refine ⟨8969659246833589986895759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11959545662444786649194345 8969659246833589986895759)
    ·
      refine ⟨13454488870250384980343639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8969659246833589986895759 13454488870250384980343639)
      ·
        refine ⟨20181733305375577470515459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13454488870250384980343639 20181733305375577470515459)
        ·
          refine ⟨30272599958063366205773189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20181733305375577470515459 30272599958063366205773189)
          ·
            refine ⟨5676112492136881163582473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30272599958063366205773189 5676112492136881163582473)
            ·
              refine ⟨4257084369102660872686855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5676112492136881163582473 4257084369102660872686855)
              ·
                refine ⟨6385626553653991309030283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4257084369102660872686855 6385626553653991309030283)
                ·
                  refine ⟨9578439830480986963545425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6385626553653991309030283 9578439830480986963545425)
                  ·
                    refine ⟨7183829872860740222659069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9578439830480986963545425 7183829872860740222659069)
                    ·
                      refine ⟨2693936202322777583497151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7183829872860740222659069 2693936202322777583497151)
                      ·
                        rfl

theorem cell23_5246422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_5246422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5246422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5246422 prefixEnd_5246422 := by exact prefixLift 5246422
  have htrace : WordTrace (prefixWord ++ tailWord_5246422) baseStart_5246422 baseEnd_5246422 := by
    simpa [prefixWord, tailWord_5246422, baseEnd_5246422] using wordTrace_append hprefix tailTrace_5246422
  have hstable : (prefixWord ++ tailWord_5246422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5246422).length < 2 ^ (prefixWord ++ tailWord_5246422).sum := by decide
  have hdescent : baseEnd_5246422 < baseStart_5246422 := by decide
  rcases family_descends (prefixWord ++ tailWord_5246422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5246435 : List Nat := [1, 1, 1, 6, 2, 3, 1, 2, 2, 1, 3]
def baseStart_5246435 : Nat := 118140960795 + 5246435 * 2 ^ 59
def prefixEnd_5246435 : Nat := 4983230072969 + 3 ^ 40 * 5246435 * 2
def baseEnd_5246435 : Nat := 2693942877571286032634591

theorem tailTrace_5246435 : CollatzResearch.WordTrace tailWord_5246435 prefixEnd_5246435 2693942877571286032634591 := by
  unfold tailWord_5246435
  simp only [CollatzResearch.WordTrace]
  refine ⟨191353204748069489607332759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127568803165379659738221839 191353204748069489607332759)
  ·
    refine ⟨287029807122104234410999139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191353204748069489607332759 287029807122104234410999139)
    ·
      refine ⟨430544710683156351616498709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287029807122104234410999139 430544710683156351616498709)
      ·
        refine ⟨20181783313272953982023377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 430544710683156351616498709 20181783313272953982023377)
        ·
          refine ⟨15136337484954715486517533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20181783313272953982023377 15136337484954715486517533)
          ·
            refine ⟨5676126556858018307444075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15136337484954715486517533 5676126556858018307444075)
            ·
              refine ⟨8514189835287027461166113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5676126556858018307444075 8514189835287027461166113)
              ·
                refine ⟨6385642376465270595874585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8514189835287027461166113 6385642376465270595874585)
                ·
                  refine ⟨4789231782348952946905939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6385642376465270595874585 4789231782348952946905939)
                  ·
                    refine ⟨7183847673523429420358909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4789231782348952946905939 7183847673523429420358909)
                    ·
                      refine ⟨2693942877571286032634591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7183847673523429420358909 2693942877571286032634591)
                      ·
                        rfl

theorem cell23_5246435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_5246435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5246435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5246435 prefixEnd_5246435 := by exact prefixLift 5246435
  have htrace : WordTrace (prefixWord ++ tailWord_5246435) baseStart_5246435 baseEnd_5246435 := by
    simpa [prefixWord, tailWord_5246435, baseEnd_5246435] using wordTrace_append hprefix tailTrace_5246435
  have hstable : (prefixWord ++ tailWord_5246435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5246435).length < 2 ^ (prefixWord ++ tailWord_5246435).sum := by decide
  have hdescent : baseEnd_5246435 < baseStart_5246435 := by decide
  rcases family_descends (prefixWord ++ tailWord_5246435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5246444 : List Nat := [2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 3]
def baseStart_5246444 : Nat := 118140960795 + 5246444 * 2 ^ 59
def prefixEnd_5246444 : Nat := 4983230072969 + 3 ^ 40 * 5246444 * 2
def baseEnd_5246444 : Nat := 2693947498897176497422049

theorem tailTrace_5246444 : CollatzResearch.WordTrace tailWord_5246444 prefixEnd_5246444 2693947498897176497422049 := by
  unfold tailWord_5246444
  simp only [CollatzResearch.WordTrace]
  refine ⟨95676766502518442072205193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127569022003357922762940257 95676766502518442072205193)
  ·
    refine ⟨71757574876888831554153895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95676766502518442072205193 71757574876888831554153895)
    ·
      refine ⟨107636362315333247331230843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71757574876888831554153895 107636362315333247331230843)
      ·
        refine ⟨161454543472999870996846265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107636362315333247331230843 161454543472999870996846265)
        ·
          refine ⟨121090907604749903247634699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161454543472999870996846265 121090907604749903247634699)
          ·
            refine ⟨181636361407124854871452049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121090907604749903247634699 181636361407124854871452049)
            ·
              refine ⟨136227271055343641153589037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 181636361407124854871452049 136227271055343641153589037)
              ·
                refine ⟨51085226645753865432595889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 136227271055343641153589037 51085226645753865432595889)
                ·
                  refine ⟨38313919984315399074446917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51085226645753865432595889 38313919984315399074446917)
                  ·
                    refine ⟨7183859997059137326458797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38313919984315399074446917 7183859997059137326458797)
                    ·
                      refine ⟨2693947498897176497422049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7183859997059137326458797 2693947498897176497422049)
                      ·
                        rfl

theorem cell23_5246444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 3].length) (baseStart_5246444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5246444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5246444 prefixEnd_5246444 := by exact prefixLift 5246444
  have htrace : WordTrace (prefixWord ++ tailWord_5246444) baseStart_5246444 baseEnd_5246444 := by
    simpa [prefixWord, tailWord_5246444, baseEnd_5246444] using wordTrace_append hprefix tailTrace_5246444
  have hstable : (prefixWord ++ tailWord_5246444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5246444).length < 2 ^ (prefixWord ++ tailWord_5246444).sum := by decide
  have hdescent : baseEnd_5246444 < baseStart_5246444 := by decide
  rcases family_descends (prefixWord ++ tailWord_5246444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5246470 : List Nat := [6, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2]
def baseStart_5246470 : Nat := 118140960795 + 5246470 * 2 ^ 59
def prefixEnd_5246470 : Nat := 4983230072969 + 3 ^ 40 * 5246470 * 2
def baseEnd_5246470 : Nat := 2693960849394193395696931

theorem tailTrace_5246470 : CollatzResearch.WordTrace tailWord_5246470 prefixEnd_5246470 2693960849394193395696931 := by
  unfold tailWord_5246470
  simp only [CollatzResearch.WordTrace]
  refine ⟨5979827540716959080776777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 127569654201961793723237909 5979827540716959080776777)
  ·
    refine ⟨4484870655537719310582583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5979827540716959080776777 4484870655537719310582583)
    ·
      refine ⟨6727305983306578965873875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4484870655537719310582583 6727305983306578965873875)
      ·
        refine ⟨10090958974959868448810813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6727305983306578965873875 10090958974959868448810813)
        ·
          refine ⟨3784109615609950668304055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10090958974959868448810813 3784109615609950668304055)
          ·
            refine ⟨5676164423414926002456083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3784109615609950668304055 5676164423414926002456083)
            ·
              refine ⟨8514246635122389003684125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5676164423414926002456083 8514246635122389003684125)
              ·
                refine ⟨3192842488170895876381547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8514246635122389003684125 3192842488170895876381547)
                ·
                  refine ⟨4789263732256343814572321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3192842488170895876381547 4789263732256343814572321)
                  ·
                    refine ⟨3591947799192257860929241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4789263732256343814572321 3591947799192257860929241)
                    ·
                      refine ⟨2693960849394193395696931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3591947799192257860929241 2693960849394193395696931)
                      ·
                        rfl

theorem cell23_5246470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_5246470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5246470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5246470 prefixEnd_5246470 := by exact prefixLift 5246470
  have htrace : WordTrace (prefixWord ++ tailWord_5246470) baseStart_5246470 baseEnd_5246470 := by
    simpa [prefixWord, tailWord_5246470, baseEnd_5246470] using wordTrace_append hprefix tailTrace_5246470
  have hstable : (prefixWord ++ tailWord_5246470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5246470).length < 2 ^ (prefixWord ++ tailWord_5246470).sum := by decide
  have hdescent : baseEnd_5246470 < baseStart_5246470 := by decide
  rcases family_descends (prefixWord ++ tailWord_5246470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5246501 : List Nat := [1, 3, 1, 2, 2, 1, 1, 3, 2, 5, 2]
def baseStart_5246501 : Nat := 118140960795 + 5246501 * 2 ^ 59
def prefixEnd_5246501 : Nat := 4983230072969 + 3 ^ 40 * 5246501 * 2
def baseEnd_5246501 : Nat := 2693976767294482774409287

theorem tailTrace_5246501 : CollatzResearch.WordTrace tailWord_5246501 prefixEnd_5246501 2693976767294482774409287 := by
  unfold tailWord_5246501
  simp only [CollatzResearch.WordTrace]
  refine ⟨191355611965830382879235357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127570407977220255252823571 191355611965830382879235357)
  ·
    refine ⟨71758354487186393579713259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191355611965830382879235357 71758354487186393579713259)
    ·
      refine ⟨107637531730779590369569889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71758354487186393579713259 107637531730779590369569889)
      ·
        refine ⟨80728148798084692777177417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107637531730779590369569889 80728148798084692777177417)
        ·
          refine ⟨60546111598563519582883063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80728148798084692777177417 60546111598563519582883063)
          ·
            refine ⟨90819167397845279374324595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60546111598563519582883063 90819167397845279374324595)
            ·
              refine ⟨136228751096767919061486893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90819167397845279374324595 136228751096767919061486893)
              ·
                refine ⟨51085781661287969648057585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 136228751096767919061486893 51085781661287969648057585)
                ·
                  refine ⟨38314336245965977236043189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51085781661287969648057585 38314336245965977236043189)
                  ·
                    refine ⟨3591969023059310365879049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38314336245965977236043189 3591969023059310365879049)
                    ·
                      refine ⟨2693976767294482774409287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3591969023059310365879049 2693976767294482774409287)
                      ·
                        rfl

theorem cell23_5246501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 5, 2].length) (baseStart_5246501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5246501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5246501 prefixEnd_5246501 := by exact prefixLift 5246501
  have htrace : WordTrace (prefixWord ++ tailWord_5246501) baseStart_5246501 baseEnd_5246501 := by
    simpa [prefixWord, tailWord_5246501, baseEnd_5246501] using wordTrace_append hprefix tailTrace_5246501
  have hstable : (prefixWord ++ tailWord_5246501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5246501).length < 2 ^ (prefixWord ++ tailWord_5246501).sum := by decide
  have hdescent : baseEnd_5246501 < baseStart_5246501 := by decide
  rcases family_descends (prefixWord ++ tailWord_5246501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5246531 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 6, 4, 2]
def baseStart_5246531 : Nat := 118140960795 + 5246531 * 2 ^ 59
def prefixEnd_5246531 : Nat := 4983230072969 + 3 ^ 40 * 5246531 * 2
def baseEnd_5246531 : Nat := 2693992171714117657034149

theorem tailTrace_5246531 : CollatzResearch.WordTrace tailWord_5246531 prefixEnd_5246531 2693992171714117657034149 := by
  unfold tailWord_5246531
  simp only [CollatzResearch.WordTrace]
  refine ⟨191356706155721698002827447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127571137437147798668551631 191356706155721698002827447)
  ·
    refine ⟨287035059233582547004241171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191356706155721698002827447 287035059233582547004241171)
    ·
      refine ⟨430552588850373820506361757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287035059233582547004241171 430552588850373820506361757)
      ·
        refine ⟨161457220818890182689885659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 430552588850373820506361757 161457220818890182689885659)
        ·
          refine ⟨242185831228335274034828489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161457220818890182689885659 242185831228335274034828489)
          ·
            refine ⟨181639373421251455526121367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 242185831228335274034828489 181639373421251455526121367)
            ·
              refine ⟨272459060131877183289182051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181639373421251455526121367 272459060131877183289182051)
              ·
                refine ⟨408688590197815774933773077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 272459060131877183289182051 408688590197815774933773077)
                ·
                  refine ⟨19157277665522614450020613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 408688590197815774933773077 19157277665522614450020613)
                  ·
                    refine ⟨3591989562285490209378865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19157277665522614450020613 3591989562285490209378865)
                    ·
                      refine ⟨2693992171714117657034149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3591989562285490209378865 2693992171714117657034149)
                      ·
                        rfl

theorem cell23_5246531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 6, 4, 2].length) (baseStart_5246531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5246531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5246531 prefixEnd_5246531 := by exact prefixLift 5246531
  have htrace : WordTrace (prefixWord ++ tailWord_5246531) baseStart_5246531 baseEnd_5246531 := by
    simpa [prefixWord, tailWord_5246531, baseEnd_5246531] using wordTrace_append hprefix tailTrace_5246531
  have hstable : (prefixWord ++ tailWord_5246531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5246531).length < 2 ^ (prefixWord ++ tailWord_5246531).sum := by decide
  have hdescent : baseEnd_5246531 < baseStart_5246531 := by decide
  rcases family_descends (prefixWord ++ tailWord_5246531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5246544 : List Nat := [2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 6]
def baseStart_5246544 : Nat := 118140960795 + 5246544 * 2 ^ 59
def prefixEnd_5246544 : Nat := 4983230072969 + 3 ^ 40 * 5246544 * 2
def baseEnd_5246544 : Nat := 2693998846962626106171589

theorem tailTrace_5246544 : CollatzResearch.WordTrace tailWord_5246544 prefixEnd_5246544 2693998846962626106171589 := by
  unfold tailWord_5246544
  simp only [CollatzResearch.WordTrace]
  refine ⟨95678590152337300611525343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127571453536449734148700457 95678590152337300611525343)
  ·
    refine ⟨143517885228505950917288015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95678590152337300611525343 143517885228505950917288015)
    ·
      refine ⟨215276827842758926375932023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143517885228505950917288015 215276827842758926375932023)
      ·
        refine ⟨322915241764138389563898035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215276827842758926375932023 322915241764138389563898035)
        ·
          refine ⟨484372862646207584345847053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322915241764138389563898035 484372862646207584345847053)
          ·
            refine ⟨181639823492327844129692645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 484372862646207584345847053 181639823492327844129692645)
            ·
              refine ⟨34057466904811470774317371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 181639823492327844129692645 34057466904811470774317371)
              ·
                refine ⟨51086200357217206161476057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34057466904811470774317371 51086200357217206161476057)
                ·
                  refine ⟨38314650267912904621107043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51086200357217206161476057 38314650267912904621107043)
                  ·
                    refine ⟨57471975401869356931660565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38314650267912904621107043 57471975401869356931660565)
                    ·
                      refine ⟨2693998846962626106171589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57471975401869356931660565 2693998846962626106171589)
                      ·
                        rfl

theorem cell23_5246544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 6].length) (baseStart_5246544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5246544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5246544 prefixEnd_5246544 := by exact prefixLift 5246544
  have htrace : WordTrace (prefixWord ++ tailWord_5246544) baseStart_5246544 baseEnd_5246544 := by
    simpa [prefixWord, tailWord_5246544, baseEnd_5246544] using wordTrace_append hprefix tailTrace_5246544
  have hstable : (prefixWord ++ tailWord_5246544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5246544).length < 2 ^ (prefixWord ++ tailWord_5246544).sum := by decide
  have hdescent : baseEnd_5246544 < baseStart_5246544 := by decide
  rcases family_descends (prefixWord ++ tailWord_5246544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5246548 : List Nat := [2, 4, 1, 1, 1, 2, 2, 2, 2, 4, 2]
def baseStart_5246548 : Nat := 118140960795 + 5246548 * 2 ^ 59
def prefixEnd_5246548 : Nat := 4983230072969 + 3 ^ 40 * 5246548 * 2
def baseEnd_5246548 : Nat := 2694000900885244090521571

theorem tailTrace_5246548 : CollatzResearch.WordTrace tailWord_5246548 prefixEnd_5246548 2694000900885244090521571 := by
  unfold tailWord_5246548
  simp only [CollatzResearch.WordTrace]
  refine ⟨95678663098330054953098149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127571550797773406604130865 95678663098330054953098149)
  ·
    refine ⟨17939749330936885303705903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95678663098330054953098149 17939749330936885303705903)
    ·
      refine ⟨26909623996405327955558855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17939749330936885303705903 26909623996405327955558855)
      ·
        refine ⟨40364435994607991933338283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26909623996405327955558855 40364435994607991933338283)
        ·
          refine ⟨60546653991911987900007425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40364435994607991933338283 60546653991911987900007425)
          ·
            refine ⟨45409990493933990925005569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60546653991911987900007425 45409990493933990925005569)
            ·
              refine ⟨34057492870450493193754177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45409990493933990925005569 34057492870450493193754177)
              ·
                refine ⟨25543119652837869895315633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34057492870450493193754177 25543119652837869895315633)
                ·
                  refine ⟨19157339739628402421486725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25543119652837869895315633 19157339739628402421486725)
                  ·
                    refine ⟨3592001201180325454028761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19157339739628402421486725 3592001201180325454028761)
                    ·
                      refine ⟨2694000900885244090521571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3592001201180325454028761 2694000900885244090521571)
                      ·
                        rfl

theorem cell23_5246548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 2, 4, 2].length) (baseStart_5246548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5246548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5246548 prefixEnd_5246548 := by exact prefixLift 5246548
  have htrace : WordTrace (prefixWord ++ tailWord_5246548) baseStart_5246548 baseEnd_5246548 := by
    simpa [prefixWord, tailWord_5246548, baseEnd_5246548] using wordTrace_append hprefix tailTrace_5246548
  have hstable : (prefixWord ++ tailWord_5246548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5246548).length < 2 ^ (prefixWord ++ tailWord_5246548).sum := by decide
  have hdescent : baseEnd_5246548 < baseStart_5246548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5246548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5246554 : List Nat := [3, 1, 1, 2, 1, 1, 1, 5, 8]
def baseStart_5246554 : Nat := 118140960795 + 5246554 * 2 ^ 59
def prefixEnd_5246554 : Nat := 4983230072969 + 3 ^ 40 * 5246554 * 2
def baseEnd_5246554 : Nat := 299333775752130118560727

theorem tailTrace_5246554 : CollatzResearch.WordTrace tailWord_5246554 prefixEnd_5246554 299333775752130118560727 := by
  unfold tailWord_5246554
  simp only [CollatzResearch.WordTrace]
  refine ⟨47839386258659593232728679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127571696689758915287276477 47839386258659593232728679)
  ·
    refine ⟨71759079387989389849093019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47839386258659593232728679 71759079387989389849093019)
    ·
      refine ⟨107638619081984084773639529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71759079387989389849093019 107638619081984084773639529)
      ·
        refine ⟨80728964311488063580229647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107638619081984084773639529 80728964311488063580229647)
        ·
          refine ⟨121093446467232095370344471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80728964311488063580229647 121093446467232095370344471)
          ·
            refine ⟨181640169700848143055516707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121093446467232095370344471 181640169700848143055516707)
            ·
              refine ⟨272460254551272214583275061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181640169700848143055516707 272460254551272214583275061)
              ·
                refine ⟨25543148864181770117182037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 272460254551272214583275061 25543148864181770117182037)
                ·
                  refine ⟨299333775752130118560727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25543148864181770117182037 299333775752130118560727)
                  ·
                    rfl

theorem cell23_5246554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 8].length) (baseStart_5246554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5246554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5246554 prefixEnd_5246554 := by exact prefixLift 5246554
  have htrace : WordTrace (prefixWord ++ tailWord_5246554) baseStart_5246554 baseEnd_5246554 := by
    simpa [prefixWord, tailWord_5246554, baseEnd_5246554] using wordTrace_append hprefix tailTrace_5246554
  have hstable : (prefixWord ++ tailWord_5246554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5246554).length < 2 ^ (prefixWord ++ tailWord_5246554).sum := by decide
  have hdescent : baseEnd_5246554 < baseStart_5246554 := by decide
  rcases family_descends (prefixWord ++ tailWord_5246554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5246608 : List Nat := [2, 1, 1, 1, 1, 1, 3, 6, 2, 3, 2]
def baseStart_5246608 : Nat := 118140960795 + 5246608 * 2 ^ 59
def prefixEnd_5246608 : Nat := 4983230072969 + 3 ^ 40 * 5246608 * 2
def baseEnd_5246608 : Nat := 2694031709724513855771295

theorem tailTrace_5246608 : CollatzResearch.WordTrace tailWord_5246608 prefixEnd_5246608 2694031709724513855771295 := by
  unfold tailWord_5246608
  simp only [CollatzResearch.WordTrace]
  refine ⟨95679757288221370076690239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127573009717628493435586985 95679757288221370076690239)
  ·
    refine ⟨143519635932332055115035359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95679757288221370076690239 143519635932332055115035359)
    ·
      refine ⟨215279453898498082672553039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143519635932332055115035359 215279453898498082672553039)
      ·
        refine ⟨322919180847747124008829559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215279453898498082672553039 322919180847747124008829559)
        ·
          refine ⟨484378771271620686013244339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322919180847747124008829559 484378771271620686013244339)
          ·
            refine ⟨726568156907431029019866509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 484378771271620686013244339 726568156907431029019866509)
            ·
              refine ⟨272463058840286635882449941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 726568156907431029019866509 272463058840286635882449941)
              ·
                refine ⟨12771705883138436056989841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 272463058840286635882449941 12771705883138436056989841)
                ·
                  refine ⟨9578779412353827042742381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12771705883138436056989841 9578779412353827042742381)
                  ·
                    refine ⟨3592042279632685141028393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9578779412353827042742381 3592042279632685141028393)
                    ·
                      refine ⟨2694031709724513855771295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3592042279632685141028393 2694031709724513855771295)
                      ·
                        rfl

theorem cell23_5246608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 6, 2, 3, 2].length) (baseStart_5246608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5246608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5246608 prefixEnd_5246608 := by exact prefixLift 5246608
  have htrace : WordTrace (prefixWord ++ tailWord_5246608) baseStart_5246608 baseEnd_5246608 := by
    simpa [prefixWord, tailWord_5246608, baseEnd_5246608] using wordTrace_append hprefix tailTrace_5246608
  have hstable : (prefixWord ++ tailWord_5246608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5246608).length < 2 ^ (prefixWord ++ tailWord_5246608).sum := by decide
  have hdescent : baseEnd_5246608 < baseStart_5246608 := by decide
  rcases family_descends (prefixWord ++ tailWord_5246608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5246615 : List Nat := [1, 1, 3, 3, 2, 3, 2, 1, 3, 1, 3]
def baseStart_5246615 : Nat := 118140960795 + 5246615 * 2 ^ 59
def prefixEnd_5246615 : Nat := 4983230072969 + 3 ^ 40 * 5246615 * 2
def baseEnd_5246615 : Nat := 2694035304089095328383763

theorem tailTrace_5246615 : CollatzResearch.WordTrace tailWord_5246615 prefixEnd_5246615 2694035304089095328383763 := by
  unfold tailWord_5246615
  simp only [CollatzResearch.WordTrace]
  refine ⟨191359769887417380348885299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127573179924944920232590199 191359769887417380348885299)
  ·
    refine ⟨287039654831126070523327949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191359769887417380348885299 287039654831126070523327949)
    ·
      refine ⟨107639870561672276446247981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 287039654831126070523327949 107639870561672276446247981)
      ·
        refine ⟨40364951460627103667342993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107639870561672276446247981 40364951460627103667342993)
        ·
          refine ⟨30273713595470327750507245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40364951460627103667342993 30273713595470327750507245)
          ·
            refine ⟨11352642598301372906440217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30273713595470327750507245 11352642598301372906440217)
            ·
              refine ⟨8514481948726029679830163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11352642598301372906440217 8514481948726029679830163)
              ·
                refine ⟨12771722923089044519745245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8514481948726029679830163 12771722923089044519745245)
                ·
                  refine ⟨4789396096158391694904467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12771722923089044519745245 4789396096158391694904467)
                  ·
                    refine ⟨7184094144237587542356701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4789396096158391694904467 7184094144237587542356701)
                    ·
                      refine ⟨2694035304089095328383763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7184094144237587542356701 2694035304089095328383763)
                      ·
                        rfl

theorem cell23_5246615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 1, 3, 1, 3].length) (baseStart_5246615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5246615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5246615 prefixEnd_5246615 := by exact prefixLift 5246615
  have htrace : WordTrace (prefixWord ++ tailWord_5246615) baseStart_5246615 baseEnd_5246615 := by
    simpa [prefixWord, tailWord_5246615, baseEnd_5246615] using wordTrace_append hprefix tailTrace_5246615
  have hstable : (prefixWord ++ tailWord_5246615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5246615).length < 2 ^ (prefixWord ++ tailWord_5246615).sum := by decide
  have hdescent : baseEnd_5246615 < baseStart_5246615 := by decide
  rcases family_descends (prefixWord ++ tailWord_5246615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5246651 : List Nat := [1, 1, 1, 1, 1, 2, 3, 6, 1, 2, 4]
def baseStart_5246651 : Nat := 118140960795 + 5246651 * 2 ^ 59
def prefixEnd_5246651 : Nat := 4983230072969 + 3 ^ 40 * 5246651 * 2
def baseEnd_5246651 : Nat := 2694053789392657187533597

theorem tailTrace_5246651 : CollatzResearch.WordTrace tailWord_5246651 prefixEnd_5246651 2694053789392657187533597 := by
  unfold tailWord_5246651
  simp only [CollatzResearch.WordTrace]
  refine ⟨191361082915286958497195807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127574055276857972331463871 191361082915286958497195807)
  ·
    refine ⟨287041624372930437745793711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191361082915286958497195807 287041624372930437745793711)
    ·
      refine ⟨430562436559395656618690567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287041624372930437745793711 430562436559395656618690567)
      ·
        refine ⟨645843654839093484928035851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 430562436559395656618690567 645843654839093484928035851)
        ·
          refine ⟨968765482258640227392053777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 645843654839093484928035851 968765482258640227392053777)
          ·
            refine ⟨726574111693980170544040333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 968765482258640227392053777 726574111693980170544040333)
            ·
              refine ⟨272465291885242563954015125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 726574111693980170544040333 272465291885242563954015125)
              ·
                refine ⟨12771810557120745185344459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 272465291885242563954015125 12771810557120745185344459)
                ·
                  refine ⟨19157715835681117778016689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12771810557120745185344459 19157715835681117778016689)
                  ·
                    refine ⟨14368286876760838333512517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19157715835681117778016689 14368286876760838333512517)
                    ·
                      refine ⟨2694053789392657187533597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14368286876760838333512517 2694053789392657187533597)
                      ·
                        rfl

theorem cell23_5246651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6, 1, 2, 4].length) (baseStart_5246651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5246651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5246651 prefixEnd_5246651 := by exact prefixLift 5246651
  have htrace : WordTrace (prefixWord ++ tailWord_5246651) baseStart_5246651 baseEnd_5246651 := by
    simpa [prefixWord, tailWord_5246651, baseEnd_5246651] using wordTrace_append hprefix tailTrace_5246651
  have hstable : (prefixWord ++ tailWord_5246651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5246651).length < 2 ^ (prefixWord ++ tailWord_5246651).sum := by decide
  have hdescent : baseEnd_5246651 < baseStart_5246651 := by decide
  rcases family_descends (prefixWord ++ tailWord_5246651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5246682 : List Nat := [3, 1, 1, 2, 2, 5, 2, 1, 2, 4]
def baseStart_5246682 : Nat := 118140960795 + 5246682 * 2 ^ 59
def prefixEnd_5246682 : Nat := 4983230072969 + 3 ^ 40 * 5246682 * 2
def baseEnd_5246682 : Nat := 898023235764315522081985

theorem tailTrace_5246682 : CollatzResearch.WordTrace tailWord_5246682 prefixEnd_5246682 898023235764315522081985 := by
  unfold tailWord_5246682
  simp only [CollatzResearch.WordTrace]
  refine ⟨47840553394543662697893575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127574809052116433861049533 47840553394543662697893575)
  ·
    refine ⟨71760830091815494046840363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47840553394543662697893575 71760830091815494046840363)
    ·
      refine ⟨107641245137723241070260545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71760830091815494046840363 107641245137723241070260545)
      ·
        refine ⟨80730933853292430802695409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107641245137723241070260545 80730933853292430802695409)
        ·
          refine ⟨60548200389969323102021557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80730933853292430802695409 60548200389969323102021557)
          ·
            refine ⟨5676393786559624040814521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60548200389969323102021557 5676393786559624040814521)
            ·
              refine ⟨4257295339919718030610891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5676393786559624040814521 4257295339919718030610891)
              ·
                refine ⟨6385943009879577045916337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4257295339919718030610891 6385943009879577045916337)
                ·
                  refine ⟨4789457257409682784437253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6385943009879577045916337 4789457257409682784437253)
                  ·
                    refine ⟨898023235764315522081985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4789457257409682784437253 898023235764315522081985)
                    ·
                      rfl

theorem cell23_5246682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 2, 1, 2, 4].length) (baseStart_5246682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5246682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5246682 prefixEnd_5246682 := by exact prefixLift 5246682
  have htrace : WordTrace (prefixWord ++ tailWord_5246682) baseStart_5246682 baseEnd_5246682 := by
    simpa [prefixWord, tailWord_5246682, baseEnd_5246682] using wordTrace_append hprefix tailTrace_5246682
  have hstable : (prefixWord ++ tailWord_5246682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5246682).length < 2 ^ (prefixWord ++ tailWord_5246682).sum := by decide
  have hdescent : baseEnd_5246682 < baseStart_5246682 := by decide
  rcases family_descends (prefixWord ++ tailWord_5246682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5246731 : List Nat := [1, 1, 1, 1, 5, 1, 2, 2, 1, 3, 5]
def baseStart_5246731 : Nat := 118140960795 + 5246731 * 2 ^ 59
def prefixEnd_5246731 : Nat := 4983230072969 + 3 ^ 40 * 5246731 * 2
def baseEnd_5246731 : Nat := 2694094867845016874533229

theorem tailTrace_5246731 : CollatzResearch.WordTrace tailWord_5246731 prefixEnd_5246731 2694094867845016874533229 := by
  unfold tailWord_5246731
  simp only [CollatzResearch.WordTrace]
  refine ⟨191364000754997132160108047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127576000503331421440072031 191364000754997132160108047)
  ·
    refine ⟨287046001132495698240162071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191364000754997132160108047 287046001132495698240162071)
    ·
      refine ⟨430569001698743547360243107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287046001132495698240162071 430569001698743547360243107)
      ·
        refine ⟨645853502548115321040364661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 430569001698743547360243107 645853502548115321040364661)
        ·
          refine ⟨60548765863885811347534187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 645853502548115321040364661 60548765863885811347534187)
          ·
            refine ⟨90823148795828717021301281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60548765863885811347534187 90823148795828717021301281)
            ·
              refine ⟨68117361596871537765975961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90823148795828717021301281 68117361596871537765975961)
              ·
                refine ⟨51088021197653653324481971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68117361596871537765975961 51088021197653653324481971)
                ·
                  refine ⟨76632031796480479986722957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51088021197653653324481971 76632031796480479986722957)
                  ·
                    refine ⟨28737011923680179995021109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 76632031796480479986722957 28737011923680179995021109)
                    ·
                      refine ⟨2694094867845016874533229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28737011923680179995021109 2694094867845016874533229)
                      ·
                        rfl

theorem cell23_5246731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 3, 5].length) (baseStart_5246731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5246731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5246731 prefixEnd_5246731 := by exact prefixLift 5246731
  have htrace : WordTrace (prefixWord ++ tailWord_5246731) baseStart_5246731 baseEnd_5246731 := by
    simpa [prefixWord, tailWord_5246731, baseEnd_5246731] using wordTrace_append hprefix tailTrace_5246731
  have hstable : (prefixWord ++ tailWord_5246731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5246731).length < 2 ^ (prefixWord ++ tailWord_5246731).sum := by decide
  have hdescent : baseEnd_5246731 < baseStart_5246731 := by decide
  rcases family_descends (prefixWord ++ tailWord_5246731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5246748 : List Nat := [2, 2, 3, 1, 1, 2, 1, 2, 2, 4, 3]
def baseStart_5246748 : Nat := 118140960795 + 5246748 * 2 ^ 59
def prefixEnd_5246748 : Nat := 4983230072969 + 3 ^ 40 * 5246748 * 2
def baseEnd_5246748 : Nat := 2694103597016143308020651

theorem tailTrace_5246748 : CollatzResearch.WordTrace tailWord_5246748 prefixEnd_5246748 2694103597016143308020651 := by
  unfold tailWord_5246748
  simp only [CollatzResearch.WordTrace]
  refine ⟨95682310397967772031738449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127576413863957029375651265 95682310397967772031738449)
  ·
    refine ⟨71761732798475829023803837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95682310397967772031738449 71761732798475829023803837)
    ·
      refine ⟨26910649799428435883926439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71761732798475829023803837 26910649799428435883926439)
      ·
        refine ⟨40365974699142653825889659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26910649799428435883926439 40365974699142653825889659)
        ·
          refine ⟨60548962048713980738834489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40365974699142653825889659 60548962048713980738834489)
          ·
            refine ⟨45411721536535485554125867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60548962048713980738834489 45411721536535485554125867)
            ·
              refine ⟨68117582304803228331188801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45411721536535485554125867 68117582304803228331188801)
              ·
                refine ⟨51088186728602421248391601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68117582304803228331188801 51088186728602421248391601)
                ·
                  refine ⟨38316140046451815936293701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51088186728602421248391601 38316140046451815936293701)
                  ·
                    refine ⟨7184276258709715488055069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38316140046451815936293701 7184276258709715488055069)
                    ·
                      refine ⟨2694103597016143308020651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7184276258709715488055069 2694103597016143308020651)
                      ·
                        rfl

theorem cell23_5246748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_5246748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5246748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5246748 prefixEnd_5246748 := by exact prefixLift 5246748
  have htrace : WordTrace (prefixWord ++ tailWord_5246748) baseStart_5246748 baseEnd_5246748 := by
    simpa [prefixWord, tailWord_5246748, baseEnd_5246748] using wordTrace_append hprefix tailTrace_5246748
  have hstable : (prefixWord ++ tailWord_5246748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5246748).length < 2 ^ (prefixWord ++ tailWord_5246748).sum := by decide
  have hdescent : baseEnd_5246748 < baseStart_5246748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5246748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5246796 : List Nat := [2, 2, 1, 3, 4, 1, 3, 1, 2, 2, 2]
def baseStart_5246796 : Nat := 118140960795 + 5246796 * 2 ^ 59
def prefixEnd_5246796 : Nat := 4983230072969 + 3 ^ 40 * 5246796 * 2
def baseEnd_5246796 : Nat := 2694128244087559120220431

theorem tailTrace_5246796 : CollatzResearch.WordTrace tailWord_5246796 prefixEnd_5246796 2694128244087559120220431 := by
  unfold tailWord_5246796
  simp only [CollatzResearch.WordTrace]
  refine ⟨95683185749880824130612121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127577580999841098840816161 95683185749880824130612121)
  ·
    refine ⟨71762389312410618097959091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95683185749880824130612121 71762389312410618097959091)
    ·
      refine ⟨107643583968615927146938637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71762389312410618097959091 107643583968615927146938637)
      ·
        refine ⟨40366343988230972680101989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107643583968615927146938637 40366343988230972680101989)
        ·
          refine ⟨7568689497793307377519123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40366343988230972680101989 7568689497793307377519123)
          ·
            refine ⟨11353034246689961066278685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7568689497793307377519123 11353034246689961066278685)
            ·
              refine ⟨4257387842508735399854507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11353034246689961066278685 4257387842508735399854507)
              ·
                refine ⟨6386081763763103099781761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4257387842508735399854507 6386081763763103099781761)
                ·
                  refine ⟨4789561322822327324836321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6386081763763103099781761 4789561322822327324836321)
                  ·
                    refine ⟨3592170992116745493627241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4789561322822327324836321 3592170992116745493627241)
                    ·
                      refine ⟨2694128244087559120220431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3592170992116745493627241 2694128244087559120220431)
                      ·
                        rfl

theorem cell23_5246796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 3, 1, 2, 2, 2].length) (baseStart_5246796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5246796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5246796 prefixEnd_5246796 := by exact prefixLift 5246796
  have htrace : WordTrace (prefixWord ++ tailWord_5246796) baseStart_5246796 baseEnd_5246796 := by
    simpa [prefixWord, tailWord_5246796, baseEnd_5246796] using wordTrace_append hprefix tailTrace_5246796
  have hstable : (prefixWord ++ tailWord_5246796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5246796).length < 2 ^ (prefixWord ++ tailWord_5246796).sum := by decide
  have hdescent : baseEnd_5246796 < baseStart_5246796 := by decide
  rcases family_descends (prefixWord ++ tailWord_5246796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5246819 : List Nat := [1, 1, 1, 5, 5, 1, 1, 3, 5]
def baseStart_5246819 : Nat := 118140960795 + 5246819 * 2 ^ 59
def prefixEnd_5246819 : Nat := 4983230072969 + 3 ^ 40 * 5246819 * 2
def baseEnd_5246819 : Nat := 299348894904734725581425

theorem tailTrace_5246819 : CollatzResearch.WordTrace tailWord_5246819 prefixEnd_5246819 299348894904734725581425 := by
  unfold tailWord_5246819
  simp only [CollatzResearch.WordTrace]
  refine ⟨191367210378678323189311511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127578140252452215459541007 191367210378678323189311511)
  ·
    refine ⟨287050815568017484783967267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191367210378678323189311511 287050815568017484783967267)
    ·
      refine ⟨430576223352026227175950901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287050815568017484783967267 430576223352026227175950901)
      ·
        refine ⟨40366520939252458797745397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 430576223352026227175950901 40366520939252458797745397)
        ·
          refine ⟨3784361338054918012288631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40366520939252458797745397 3784361338054918012288631)
          ·
            refine ⟨5676542007082377018432947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3784361338054918012288631 5676542007082377018432947)
            ·
              refine ⟨8514813010623565527649421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5676542007082377018432947 8514813010623565527649421)
              ·
                refine ⟨3193054878983837072868533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8514813010623565527649421 3193054878983837072868533)
                ·
                  refine ⟨299348894904734725581425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3193054878983837072868533 299348894904734725581425)
                  ·
                    rfl

theorem cell23_5246819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 3, 5].length) (baseStart_5246819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5246819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5246819 prefixEnd_5246819 := by exact prefixLift 5246819
  have htrace : WordTrace (prefixWord ++ tailWord_5246819) baseStart_5246819 baseEnd_5246819 := by
    simpa [prefixWord, tailWord_5246819, baseEnd_5246819] using wordTrace_append hprefix tailTrace_5246819
  have hstable : (prefixWord ++ tailWord_5246819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5246819).length < 2 ^ (prefixWord ++ tailWord_5246819).sum := by decide
  have hdescent : baseEnd_5246819 < baseStart_5246819 := by decide
  rcases family_descends (prefixWord ++ tailWord_5246819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5246898 : List Nat := [3, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5]
def baseStart_5246898 : Nat := 118140960795 + 5246898 * 2 ^ 59
def prefixEnd_5246898 : Nat := 4983230072969 + 3 ^ 40 * 5246898 * 2
def baseEnd_5246898 : Nat := 2694180619114317721144961

theorem tailTrace_5246898 : CollatzResearch.WordTrace tailWord_5246898 prefixEnd_5246898 2694180619114317721144961 := by
  unfold tailWord_5246898
  simp only [CollatzResearch.WordTrace]
  refine ⟨47842522936348029920359337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127580061163594746454291565 47842522936348029920359337)
  ·
    refine ⟨35881892202261022440269503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47842522936348029920359337 35881892202261022440269503)
    ·
      refine ⟨53822838303391533660404255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35881892202261022440269503 53822838303391533660404255)
      ·
        refine ⟨80734257455087300490606383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53822838303391533660404255 80734257455087300490606383)
        ·
          refine ⟨121101386182630950735909575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80734257455087300490606383 121101386182630950735909575)
          ·
            refine ⟨181652079273946426103864363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121101386182630950735909575 181652079273946426103864363)
            ·
              refine ⟨272478118910919639155796545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181652079273946426103864363 272478118910919639155796545)
              ·
                refine ⟨204358589183189729366847409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 272478118910919639155796545 204358589183189729366847409)
                ·
                  refine ⟨153268941887392297025135557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 204358589183189729366847409 153268941887392297025135557)
                  ·
                    refine ⟨28737926603886055692212917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 153268941887392297025135557 28737926603886055692212917)
                    ·
                      refine ⟨2694180619114317721144961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28737926603886055692212917 2694180619114317721144961)
                      ·
                        rfl

theorem cell23_5246898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_5246898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5246898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5246898 prefixEnd_5246898 := by exact prefixLift 5246898
  have htrace : WordTrace (prefixWord ++ tailWord_5246898) baseStart_5246898 baseEnd_5246898 := by
    simpa [prefixWord, tailWord_5246898, baseEnd_5246898] using wordTrace_append hprefix tailTrace_5246898
  have hstable : (prefixWord ++ tailWord_5246898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5246898).length < 2 ^ (prefixWord ++ tailWord_5246898).sum := by decide
  have hdescent : baseEnd_5246898 < baseStart_5246898 := by decide
  rcases family_descends (prefixWord ++ tailWord_5246898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5246935 : List Nat := [1, 1, 3, 2, 1, 1, 4, 2, 4, 4]
def baseStart_5246935 : Nat := 118140960795 + 5246935 * 2 ^ 59
def prefixEnd_5246935 : Nat := 4983230072969 + 3 ^ 40 * 5246935 * 2
def baseEnd_5246935 : Nat := 898066539299511358794097

theorem tailTrace_5246935 : CollatzResearch.WordTrace tailWord_5246935 prefixEnd_5246935 898066539299511358794097 := by
  unfold tailWord_5246935
  simp only [CollatzResearch.WordTrace]
  refine ⟨191371441246258075000534259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127580960830838716667022839 191371441246258075000534259)
  ·
    refine ⟨287057161869387112500801389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191371441246258075000534259 287057161869387112500801389)
    ·
      refine ⟨107646435701020167187800521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 287057161869387112500801389 107646435701020167187800521)
      ·
        refine ⟨80734826775765125390850391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107646435701020167187800521 80734826775765125390850391)
        ·
          refine ⟨121102240163647688086275587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80734826775765125390850391 121102240163647688086275587)
          ·
            refine ⟨181653360245471532129413381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121102240163647688086275587 181653360245471532129413381)
            ·
              refine ⟨34060005046025912274265009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 181653360245471532129413381 34060005046025912274265009)
              ·
                refine ⟨25545003784519434205698757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34060005046025912274265009 25545003784519434205698757)
                ·
                  refine ⟨4789688209597393913568517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25545003784519434205698757 4789688209597393913568517)
                  ·
                    refine ⟨898066539299511358794097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4789688209597393913568517 898066539299511358794097)
                    ·
                      rfl

theorem cell23_5246935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 4, 4].length) (baseStart_5246935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5246935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5246935 prefixEnd_5246935 := by exact prefixLift 5246935
  have htrace : WordTrace (prefixWord ++ tailWord_5246935) baseStart_5246935 baseEnd_5246935 := by
    simpa [prefixWord, tailWord_5246935, baseEnd_5246935] using wordTrace_append hprefix tailTrace_5246935
  have hstable : (prefixWord ++ tailWord_5246935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5246935).length < 2 ^ (prefixWord ++ tailWord_5246935).sum := by decide
  have hdescent : baseEnd_5246935 < baseStart_5246935 := by decide
  rcases family_descends (prefixWord ++ tailWord_5246935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5246948 : List Nat := [2, 3, 1, 1, 1, 1, 14]
def baseStart_5246948 : Nat := 118140960795 + 5246948 * 2 ^ 59
def prefixEnd_5246948 : Nat := 4983230072969 + 3 ^ 40 * 5246948 * 2
def baseEnd_5246948 : Nat := 33261806088235092907651

theorem tailTrace_5246948 : CollatzResearch.WordTrace tailWord_5246948 prefixEnd_5246948 33261806088235092907651 := by
  unfold tailWord_5246948
  simp only [CollatzResearch.WordTrace]
  refine ⟨95685957697605489110378749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127581276930140652147171665 95685957697605489110378749)
  ·
    refine ⟨35882234136602058416392031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95685957697605489110378749 35882234136602058416392031)
    ·
      refine ⟨53823351204903087624588047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35882234136602058416392031 53823351204903087624588047)
      ·
        refine ⟨80735026807354631436882071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53823351204903087624588047 80735026807354631436882071)
        ·
          refine ⟨121102540211031947155323107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80735026807354631436882071 121102540211031947155323107)
          ·
            refine ⟨181653810316547920732984661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121102540211031947155323107 181653810316547920732984661)
            ·
              refine ⟨33261806088235092907651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 181653810316547920732984661 33261806088235092907651)
              ·
                rfl

theorem cell23_5246948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 14].length) (baseStart_5246948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5246948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5246948 prefixEnd_5246948 := by exact prefixLift 5246948
  have htrace : WordTrace (prefixWord ++ tailWord_5246948) baseStart_5246948 baseEnd_5246948 := by
    simpa [prefixWord, tailWord_5246948, baseEnd_5246948] using wordTrace_append hprefix tailTrace_5246948
  have hstable : (prefixWord ++ tailWord_5246948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5246948).length < 2 ^ (prefixWord ++ tailWord_5246948).sum := by decide
  have hdescent : baseEnd_5246948 < baseStart_5246948 := by decide
  rcases family_descends (prefixWord ++ tailWord_5246948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5246959 : List Nat := [1, 1, 2, 1, 4, 2, 4, 1, 3, 2, 2]
def baseStart_5246959 : Nat := 118140960795 + 5246959 * 2 ^ 59
def prefixEnd_5246959 : Nat := 4983230072969 + 3 ^ 40 * 5246959 * 2
def baseEnd_5246959 : Nat := 2694211941434241982482181

theorem tailTrace_5246959 : CollatzResearch.WordTrace tailWord_5246959 prefixEnd_5246959 2694211941434241982482181 := by
  unfold tailWord_5246959
  simp only [CollatzResearch.WordTrace]
  refine ⟨191372316598171127099407931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127581544398780751399605287 191372316598171127099407931)
  ·
    refine ⟨287058474897256690649111897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191372316598171127099407931 287058474897256690649111897)
    ·
      refine ⟨215293856172942517986833923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287058474897256690649111897 215293856172942517986833923)
      ·
        refine ⟨322940784259413776980250885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215293856172942517986833923 322940784259413776980250885)
        ·
          refine ⟨60551397048640083183797041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 322940784259413776980250885 60551397048640083183797041)
          ·
            refine ⟨45413547786480062387847781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60551397048640083183797041 45413547786480062387847781)
            ·
              refine ⟨8515040209965011697721459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45413547786480062387847781 8515040209965011697721459)
              ·
                refine ⟨12772560314947517546582189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8515040209965011697721459 12772560314947517546582189)
                ·
                  refine ⟨4789710118105319079968321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12772560314947517546582189 4789710118105319079968321)
                  ·
                    refine ⟨3592282588578989309976241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4789710118105319079968321 3592282588578989309976241)
                    ·
                      refine ⟨2694211941434241982482181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3592282588578989309976241 2694211941434241982482181)
                      ·
                        rfl

theorem cell23_5246959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 1, 3, 2, 2].length) (baseStart_5246959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5246959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5246959 prefixEnd_5246959 := by exact prefixLift 5246959
  have htrace : WordTrace (prefixWord ++ tailWord_5246959) baseStart_5246959 baseEnd_5246959 := by
    simpa [prefixWord, tailWord_5246959, baseEnd_5246959] using wordTrace_append hprefix tailTrace_5246959
  have hstable : (prefixWord ++ tailWord_5246959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5246959).length < 2 ^ (prefixWord ++ tailWord_5246959).sum := by decide
  have hdescent : baseEnd_5246959 < baseStart_5246959 := by decide
  rcases family_descends (prefixWord ++ tailWord_5246959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5246969 : List Nat := [1, 2, 1, 3, 1, 5, 3, 1, 2, 4]
def baseStart_5246969 : Nat := 118140960795 + 5246969 * 2 ^ 59
def prefixEnd_5246969 : Nat := 4983230072969 + 3 ^ 40 * 5246969 * 2
def baseEnd_5246969 : Nat := 898072358746928981119045

theorem tailTrace_5246969 : CollatzResearch.WordTrace tailWord_5246969 prefixEnd_5246969 898072358746928981119045 := by
  unfold tailWord_5246969
  simp only [CollatzResearch.WordTrace]
  refine ⟨191372681328134898807271961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127581787552089932538181307 191372681328134898807271961)
  ·
    refine ⟨143529510996101174105453971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191372681328134898807271961 143529510996101174105453971)
    ·
      refine ⟨215294266494151761158180957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143529510996101174105453971 215294266494151761158180957)
      ·
        refine ⟨80735349935306910434317859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 215294266494151761158180957 80735349935306910434317859)
        ·
          refine ⟨121103024902960365651476789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80735349935306910434317859 121103024902960365651476789)
          ·
            refine ⟨11353408584652534279825949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 121103024902960365651476789 11353408584652534279825949)
            ·
              refine ⟨4257528219244700354934731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11353408584652534279825949 4257528219244700354934731)
              ·
                refine ⟨6386292328867050532402097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4257528219244700354934731 6386292328867050532402097)
                ·
                  refine ⟨4789719246650287899301573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6386292328867050532402097 4789719246650287899301573)
                  ·
                    refine ⟨898072358746928981119045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4789719246650287899301573 898072358746928981119045)
                    ·
                      rfl

theorem cell23_5246969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 3, 1, 2, 4].length) (baseStart_5246969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5246969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5246969 prefixEnd_5246969 := by exact prefixLift 5246969
  have htrace : WordTrace (prefixWord ++ tailWord_5246969) baseStart_5246969 baseEnd_5246969 := by
    simpa [prefixWord, tailWord_5246969, baseEnd_5246969] using wordTrace_append hprefix tailTrace_5246969
  have hstable : (prefixWord ++ tailWord_5246969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5246969).length < 2 ^ (prefixWord ++ tailWord_5246969).sum := by decide
  have hdescent : baseEnd_5246969 < baseStart_5246969 := by decide
  rcases family_descends (prefixWord ++ tailWord_5246969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5246996 : List Nat := [2, 4, 3, 2, 1, 1, 2, 1, 1, 1, 5]
def baseStart_5246996 : Nat := 118140960795 + 5246996 * 2 ^ 59
def prefixEnd_5246996 : Nat := 4983230072969 + 3 ^ 40 * 5246996 * 2
def baseEnd_5246996 : Nat := 2694230940218458337719511

theorem tailTrace_5246996 : CollatzResearch.WordTrace tailWord_5246996 prefixEnd_5246996 2694230940218458337719511 := by
  unfold tailWord_5246996
  simp only [CollatzResearch.WordTrace]
  refine ⟨95686833049518541209252421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127582444066024721612336561 95686833049518541209252421)
  ·
    refine ⟨17941281196784726476734829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95686833049518541209252421 17941281196784726476734829)
    ·
      refine ⟨6727980448794272428775561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17941281196784726476734829 6727980448794272428775561)
      ·
        refine ⟨5045985336595704321581671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6727980448794272428775561 5045985336595704321581671)
        ·
          refine ⟨7568978004893556482372507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5045985336595704321581671 7568978004893556482372507)
          ·
            refine ⟨11353467007340334723558761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7568978004893556482372507 11353467007340334723558761)
            ·
              refine ⟨8515100255505251042669071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11353467007340334723558761 8515100255505251042669071)
              ·
                refine ⟨12772650383257876564003607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8515100255505251042669071 12772650383257876564003607)
                ·
                  refine ⟨19158975574886814846005411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12772650383257876564003607 19158975574886814846005411)
                  ·
                    refine ⟨28738463362330222269008117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19158975574886814846005411 28738463362330222269008117)
                    ·
                      refine ⟨2694230940218458337719511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28738463362330222269008117 2694230940218458337719511)
                      ·
                        rfl

theorem cell23_5246996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_5246996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5246996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5246996 prefixEnd_5246996 := by exact prefixLift 5246996
  have htrace : WordTrace (prefixWord ++ tailWord_5246996) baseStart_5246996 baseEnd_5246996 := by
    simpa [prefixWord, tailWord_5246996, baseEnd_5246996] using wordTrace_append hprefix tailTrace_5246996
  have hstable : (prefixWord ++ tailWord_5246996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5246996).length < 2 ^ (prefixWord ++ tailWord_5246996).sum := by decide
  have hdescent : baseEnd_5246996 < baseStart_5246996 := by decide
  rcases family_descends (prefixWord ++ tailWord_5246996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5247026 : List Nat := [3, 2, 1, 1, 2, 3, 4, 1, 2, 1, 3]
def baseStart_5247026 : Nat := 118140960795 + 5247026 * 2 ^ 59
def prefixEnd_5247026 : Nat := 4983230072969 + 3 ^ 40 * 5247026 * 2
def baseEnd_5247026 : Nat := 2694246344638093220344373

theorem tailTrace_5247026 : CollatzResearch.WordTrace tailWord_5247026 prefixEnd_5247026 2694246344638093220344373 := by
  unfold tailWord_5247026
  simp only [CollatzResearch.WordTrace]
  refine ⟨47843690072232099385524233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127583173525952265028064621 47843690072232099385524233)
  ·
    refine ⟨35882767554174074539143175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47843690072232099385524233 35882767554174074539143175)
    ·
      refine ⟨53824151331261111808714763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35882767554174074539143175 53824151331261111808714763)
      ·
        refine ⟨80736226996891667713072145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53824151331261111808714763 80736226996891667713072145)
        ·
          refine ⟨60552170247668750784804109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80736226996891667713072145 60552170247668750784804109)
          ·
            refine ⟨22707063842875781544301541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60552170247668750784804109 22707063842875781544301541)
            ·
              refine ⟨4257574470539209039556539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22707063842875781544301541 4257574470539209039556539)
              ·
                refine ⟨6386361705808813559334809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4257574470539209039556539 6386361705808813559334809)
                ·
                  refine ⟨4789771279356610169501107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6386361705808813559334809 4789771279356610169501107)
                  ·
                    refine ⟨7184656919034915254251661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4789771279356610169501107 7184656919034915254251661)
                    ·
                      refine ⟨2694246344638093220344373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7184656919034915254251661 2694246344638093220344373)
                      ·
                        rfl

theorem cell23_5247026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 4, 1, 2, 1, 3].length) (baseStart_5247026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5247026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5247026 prefixEnd_5247026 := by exact prefixLift 5247026
  have htrace : WordTrace (prefixWord ++ tailWord_5247026) baseStart_5247026 baseEnd_5247026 := by
    simpa [prefixWord, tailWord_5247026, baseEnd_5247026] using wordTrace_append hprefix tailTrace_5247026
  have hstable : (prefixWord ++ tailWord_5247026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5247026).length < 2 ^ (prefixWord ++ tailWord_5247026).sum := by decide
  have hdescent : baseEnd_5247026 < baseStart_5247026 := by decide
  rcases family_descends (prefixWord ++ tailWord_5247026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5247035 : List Nat := [1, 1, 1, 1, 1, 2, 1, 6, 2, 4, 3]
def baseStart_5247035 : Nat := 118140960795 + 5247035 * 2 ^ 59
def prefixEnd_5247035 : Nat := 4983230072969 + 3 ^ 40 * 5247035 * 2
def baseEnd_5247035 : Nat := 2694250965963983685131831

theorem tailTrace_5247035 : CollatzResearch.WordTrace tailWord_5247035 prefixEnd_5247035 2694250965963983685131831 := by
  unfold tailWord_5247035
  simp only [CollatzResearch.WordTrace]
  refine ⟨191375088545895792079174559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127583392363930528052783039 191375088545895792079174559)
  ·
    refine ⟨287062632818843688118761839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191375088545895792079174559 287062632818843688118761839)
    ·
      refine ⟨430593949228265532178142759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287062632818843688118761839 430593949228265532178142759)
      ·
        refine ⟨645890923842398298267214139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 430593949228265532178142759 645890923842398298267214139)
        ·
          refine ⟨968836385763597447400821209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 645890923842398298267214139 968836385763597447400821209)
          ·
            refine ⟨726627289322698085550615907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 968836385763597447400821209 726627289322698085550615907)
            ·
              refine ⟨1089940933984047128325923861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 726627289322698085550615907 1089940933984047128325923861)
              ·
                refine ⟨51090981280502209140277681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1089940933984047128325923861 51090981280502209140277681)
                ·
                  refine ⟨38318235960376656855208261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51090981280502209140277681 38318235960376656855208261)
                  ·
                    refine ⟨7184669242570623160351549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38318235960376656855208261 7184669242570623160351549)
                    ·
                      refine ⟨2694250965963983685131831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7184669242570623160351549 2694250965963983685131831)
                      ·
                        rfl

theorem cell23_5247035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 4, 3].length) (baseStart_5247035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5247035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5247035 prefixEnd_5247035 := by exact prefixLift 5247035
  have htrace : WordTrace (prefixWord ++ tailWord_5247035) baseStart_5247035 baseEnd_5247035 := by
    simpa [prefixWord, tailWord_5247035, baseEnd_5247035] using wordTrace_append hprefix tailTrace_5247035
  have hstable : (prefixWord ++ tailWord_5247035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5247035).length < 2 ^ (prefixWord ++ tailWord_5247035).sum := by decide
  have hdescent : baseEnd_5247035 < baseStart_5247035 := by decide
  rcases family_descends (prefixWord ++ tailWord_5247035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5247045 : List Nat := [1, 3, 1, 1, 1, 3, 1, 2, 4, 2, 4]
def baseStart_5247045 : Nat := 118140960795 + 5247045 * 2 ^ 59
def prefixEnd_5247045 : Nat := 4983230072969 + 3 ^ 40 * 5247045 * 2
def baseEnd_5247045 : Nat := 2694256100770528646006785

theorem tailTrace_5247045 : CollatzResearch.WordTrace tailWord_5247045 prefixEnd_5247045 2694256100770528646006785 := by
  unfold tailWord_5247045
  simp only [CollatzResearch.WordTrace]
  refine ⟨191375453275859563787038589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127583635517239709191359059 191375453275859563787038589)
  ·
    refine ⟨71765794978447336420139471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191375453275859563787038589 71765794978447336420139471)
    ·
      refine ⟨107648692467671004630209207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71765794978447336420139471 107648692467671004630209207)
      ·
        refine ⟨161473038701506506945313811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107648692467671004630209207 161473038701506506945313811)
        ·
          refine ⟨242209558052259760417970717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161473038701506506945313811 242209558052259760417970717)
          ·
            refine ⟨90828584269597410156739019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 242209558052259760417970717 90828584269597410156739019)
            ·
              refine ⟨136242876404396115235108529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90828584269597410156739019 136242876404396115235108529)
              ·
                refine ⟨102182157303297086426331397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136242876404396115235108529 102182157303297086426331397)
                ·
                  refine ⟨19159154494368203704937137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 102182157303297086426331397 19159154494368203704937137)
                  ·
                    refine ⟨14369365870776152778702853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19159154494368203704937137 14369365870776152778702853)
                    ·
                      refine ⟨2694256100770528646006785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14369365870776152778702853 2694256100770528646006785)
                      ·
                        rfl

theorem cell23_5247045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 4, 2, 4].length) (baseStart_5247045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5247045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5247045 prefixEnd_5247045 := by exact prefixLift 5247045
  have htrace : WordTrace (prefixWord ++ tailWord_5247045) baseStart_5247045 baseEnd_5247045 := by
    simpa [prefixWord, tailWord_5247045, baseEnd_5247045] using wordTrace_append hprefix tailTrace_5247045
  have hstable : (prefixWord ++ tailWord_5247045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5247045).length < 2 ^ (prefixWord ++ tailWord_5247045).sum := by decide
  have hdescent : baseEnd_5247045 < baseStart_5247045 := by decide
  rcases family_descends (prefixWord ++ tailWord_5247045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5247053 : List Nat := [1, 6, 1, 1, 1, 1, 5, 1, 1, 3, 2]
def baseStart_5247053 : Nat := 118140960795 + 5247053 * 2 ^ 59
def prefixEnd_5247053 : Nat := 4983230072969 + 3 ^ 40 * 5247053 * 2
def baseEnd_5247053 : Nat := 2694260208615764614706749

theorem tailTrace_5247053 : CollatzResearch.WordTrace tailWord_5247053 prefixEnd_5247053 2694260208615764614706749 := by
  unfold tailWord_5247053
  simp only [CollatzResearch.WordTrace]
  refine ⟨191375745059830581153329813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127583830039887054102219875 191375745059830581153329813)
  ·
    refine ⟨8970738049679558491562335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 191375745059830581153329813 8970738049679558491562335)
    ·
      refine ⟨13456107074519337737343503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8970738049679558491562335 13456107074519337737343503)
      ·
        refine ⟨20184160611779006606015255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13456107074519337737343503 20184160611779006606015255)
        ·
          refine ⟨30276240917668509909022883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20184160611779006606015255 30276240917668509909022883)
          ·
            refine ⟨45414361376502764863534325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30276240917668509909022883 45414361376502764863534325)
            ·
              refine ⟨4257596379047134205956343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45414361376502764863534325 4257596379047134205956343)
              ·
                refine ⟨6386394568570701308934515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4257596379047134205956343 6386394568570701308934515)
                ·
                  refine ⟨9579591852856051963401773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6386394568570701308934515 9579591852856051963401773)
                  ·
                    refine ⟨3592346944821019486275665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9579591852856051963401773 3592346944821019486275665)
                    ·
                      refine ⟨2694260208615764614706749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3592346944821019486275665 2694260208615764614706749)
                      ·
                        rfl

theorem cell23_5247053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_5247053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5247053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5247053 prefixEnd_5247053 := by exact prefixLift 5247053
  have htrace : WordTrace (prefixWord ++ tailWord_5247053) baseStart_5247053 baseEnd_5247053 := by
    simpa [prefixWord, tailWord_5247053, baseEnd_5247053] using wordTrace_append hprefix tailTrace_5247053
  have hstable : (prefixWord ++ tailWord_5247053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5247053).length < 2 ^ (prefixWord ++ tailWord_5247053).sum := by decide
  have hdescent : baseEnd_5247053 < baseStart_5247053 := by decide
  rcases family_descends (prefixWord ++ tailWord_5247053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5247066 : List Nat := [3, 1, 1, 2, 1, 1, 6, 2, 2, 2, 2]
def baseStart_5247066 : Nat := 118140960795 + 5247066 * 2 ^ 59
def prefixEnd_5247066 : Nat := 4983230072969 + 3 ^ 40 * 5247066 * 2
def baseEnd_5247066 : Nat := 2694266883864273063844189

theorem tailTrace_5247066 : CollatzResearch.WordTrace tailWord_5247066 prefixEnd_5247066 2694266883864273063844189 := by
  unfold tailWord_5247066
  simp only [CollatzResearch.WordTrace]
  refine ⟨47844054802195871093388263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127584146139188989582368701 47844054802195871093388263)
  ·
    refine ⟨71766082203293806640082395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47844054802195871093388263 71766082203293806640082395)
    ·
      refine ⟨107649123304940709960123593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71766082203293806640082395 107649123304940709960123593)
      ·
        refine ⟨80736842478705532470092695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107649123304940709960123593 80736842478705532470092695)
        ·
          refine ⟨121105263718058298705139043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80736842478705532470092695 121105263718058298705139043)
          ·
            refine ⟨181657895577087448057708565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121105263718058298705139043 181657895577087448057708565)
            ·
              refine ⟨8515213855175974127705089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 181657895577087448057708565 8515213855175974127705089)
              ·
                refine ⟨6386410391381980595778817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8515213855175974127705089 6386410391381980595778817)
                ·
                  refine ⟨4789807793536485446834113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6386410391381980595778817 4789807793536485446834113)
                  ·
                    refine ⟨3592355845152364085125585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4789807793536485446834113 3592355845152364085125585)
                    ·
                      refine ⟨2694266883864273063844189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3592355845152364085125585 2694266883864273063844189)
                      ·
                        rfl

theorem cell23_5247066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 2, 2, 2, 2].length) (baseStart_5247066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5247066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5247066 prefixEnd_5247066 := by exact prefixLift 5247066
  have htrace : WordTrace (prefixWord ++ tailWord_5247066) baseStart_5247066 baseEnd_5247066 := by
    simpa [prefixWord, tailWord_5247066, baseEnd_5247066] using wordTrace_append hprefix tailTrace_5247066
  have hstable : (prefixWord ++ tailWord_5247066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5247066).length < 2 ^ (prefixWord ++ tailWord_5247066).sum := by decide
  have hdescent : baseEnd_5247066 < baseStart_5247066 := by decide
  rcases family_descends (prefixWord ++ tailWord_5247066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5247069 : List Nat := [1, 4, 4, 1, 1, 1, 1, 1, 2, 4, 3]
def baseStart_5247069 : Nat := 118140960795 + 5247069 * 2 ^ 59
def prefixEnd_5247069 : Nat := 4983230072969 + 3 ^ 40 * 5247069 * 2
def baseEnd_5247069 : Nat := 2694268424306236552106675

theorem tailTrace_5247069 : CollatzResearch.WordTrace tailWord_5247069 prefixEnd_5247069 2694268424306236552106675 := by
  unfold tailWord_5247069
  simp only [CollatzResearch.WordTrace]
  refine ⟨191376328627772615885912261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127584219085181743923941507 191376328627772615885912261)
  ·
    refine ⟨35883061617707365478608549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 191376328627772615885912261 35883061617707365478608549)
    ·
      refine ⟨6728074053320131027239103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35883061617707365478608549 6728074053320131027239103)
      ·
        refine ⟨10092111079980196540858655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6728074053320131027239103 10092111079980196540858655)
        ·
          refine ⟨15138166619970294811287983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10092111079980196540858655 15138166619970294811287983)
          ·
            refine ⟨22707249929955442216931975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15138166619970294811287983 22707249929955442216931975)
            ·
              refine ⟨34060874894933163325397963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22707249929955442216931975 34060874894933163325397963)
              ·
                refine ⟨51091312342399744988096945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34060874894933163325397963 51091312342399744988096945)
                ·
                  refine ⟨38318484256799808741072709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51091312342399744988096945 38318484256799808741072709)
                  ·
                    refine ⟨7184715798149964138951133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38318484256799808741072709 7184715798149964138951133)
                    ·
                      refine ⟨2694268424306236552106675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7184715798149964138951133 2694268424306236552106675)
                      ·
                        rfl

theorem cell23_5247069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_5247069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5247069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5247069 prefixEnd_5247069 := by exact prefixLift 5247069
  have htrace : WordTrace (prefixWord ++ tailWord_5247069) baseStart_5247069 baseEnd_5247069 := by
    simpa [prefixWord, tailWord_5247069, baseEnd_5247069] using wordTrace_append hprefix tailTrace_5247069
  have hstable : (prefixWord ++ tailWord_5247069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5247069).length < 2 ^ (prefixWord ++ tailWord_5247069).sum := by decide
  have hdescent : baseEnd_5247069 < baseStart_5247069 := by decide
  rcases family_descends (prefixWord ++ tailWord_5247069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5247199 : List Nat := [1, 1, 2, 3, 2, 1, 1, 1, 6, 3, 2]
def baseStart_5247199 : Nat := 118140960795 + 5247199 * 2 ^ 59
def prefixEnd_5247199 : Nat := 4983230072969 + 3 ^ 40 * 5247199 * 2
def baseEnd_5247199 : Nat := 2694335176791321043481077

theorem tailTrace_5247199 : CollatzResearch.WordTrace tailWord_5247199 prefixEnd_5247199 2694335176791321043481077 := by
  unfold tailWord_5247199
  simp only [CollatzResearch.WordTrace]
  refine ⟨191381070117301648088144651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127587380078201098725429767 191381070117301648088144651)
  ·
    refine ⟨287071605175952472132216977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191381070117301648088144651 287071605175952472132216977)
    ·
      refine ⟨215303703881964354099162733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287071605175952472132216977 215303703881964354099162733)
      ·
        refine ⟨80738888955736632787186025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 215303703881964354099162733 80738888955736632787186025)
        ·
          refine ⟨60554166716802474590389519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80738888955736632787186025 60554166716802474590389519)
          ·
            refine ⟨90831250075203711885584279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60554166716802474590389519 90831250075203711885584279)
            ·
              refine ⟨136246875112805567828376419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90831250075203711885584279 136246875112805567828376419)
              ·
                refine ⟨204370312669208351742564629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136246875112805567828376419 204370312669208351742564629)
                ·
                  refine ⟨9579858406369141487932717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 204370312669208351742564629 9579858406369141487932717)
                  ·
                    refine ⟨3592446902388428057974769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9579858406369141487932717 3592446902388428057974769)
                    ·
                      refine ⟨2694335176791321043481077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3592446902388428057974769 2694335176791321043481077)
                      ·
                        rfl

theorem cell23_5247199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 6, 3, 2].length) (baseStart_5247199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5247199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5247199 prefixEnd_5247199 := by exact prefixLift 5247199
  have htrace : WordTrace (prefixWord ++ tailWord_5247199) baseStart_5247199 baseEnd_5247199 := by
    simpa [prefixWord, tailWord_5247199, baseEnd_5247199] using wordTrace_append hprefix tailTrace_5247199
  have hstable : (prefixWord ++ tailWord_5247199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5247199).length < 2 ^ (prefixWord ++ tailWord_5247199).sum := by decide
  have hdescent : baseEnd_5247199 < baseStart_5247199 := by decide
  rcases family_descends (prefixWord ++ tailWord_5247199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5247226 : List Nat := [3, 1, 1, 1, 1, 6, 3, 1, 1, 5]
def baseStart_5247226 : Nat := 118140960795 + 5247226 * 2 ^ 59
def prefixEnd_5247226 : Nat := 4983230072969 + 3 ^ 40 * 5247226 * 2
def baseEnd_5247226 : Nat := 898116346922997479281151

theorem tailTrace_5247226 : CollatzResearch.WordTrace tailWord_5247226 prefixEnd_5247226 898116346922997479281151 := by
  unfold tailWord_5247226
  simp only [CollatzResearch.WordTrace]
  refine ⟨47845513722050957924844383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127588036592135887799585021 47845513722050957924844383)
  ·
    refine ⟨71768270583076436887266575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47845513722050957924844383 71768270583076436887266575)
    ·
      refine ⟨107652405874614655330899863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71768270583076436887266575 107652405874614655330899863)
      ·
        refine ⟨161478608811921982996349795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107652405874614655330899863 161478608811921982996349795)
        ·
          refine ⟨242217913217882974494524693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161478608811921982996349795 242217913217882974494524693)
          ·
            refine ⟨11353964682088264429430845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 242217913217882974494524693 11353964682088264429430845)
            ·
              refine ⟨4257736755783099161036567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11353964682088264429430845 4257736755783099161036567)
              ·
                refine ⟨6386605133674648741554851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4257736755783099161036567 6386605133674648741554851)
                ·
                  refine ⟨9579907700511973112332277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6386605133674648741554851 9579907700511973112332277)
                  ·
                    refine ⟨898116346922997479281151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9579907700511973112332277 898116346922997479281151)
                    ·
                      rfl

theorem cell23_5247226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 3, 1, 1, 5].length) (baseStart_5247226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5247226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5247226 prefixEnd_5247226 := by exact prefixLift 5247226
  have htrace : WordTrace (prefixWord ++ tailWord_5247226) baseStart_5247226 baseEnd_5247226 := by
    simpa [prefixWord, tailWord_5247226, baseEnd_5247226] using wordTrace_append hprefix tailTrace_5247226
  have hstable : (prefixWord ++ tailWord_5247226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5247226).length < 2 ^ (prefixWord ++ tailWord_5247226).sum := by decide
  have hdescent : baseEnd_5247226 < baseStart_5247226 := by decide
  rcases family_descends (prefixWord ++ tailWord_5247226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5247229 : List Nat := [1, 4, 1, 1, 1, 1, 1, 7, 1, 1, 4]
def baseStart_5247229 : Nat := 118140960795 + 5247229 * 2 ^ 59
def prefixEnd_5247229 : Nat := 4983230072969 + 3 ^ 40 * 5247229 * 2
def baseEnd_5247229 : Nat := 2694350581210955926105939

theorem tailTrace_5247229 : CollatzResearch.WordTrace tailWord_5247229 prefixEnd_5247229 2694350581210955926105939 := by
  unfold tailWord_5247229
  simp only [CollatzResearch.WordTrace]
  refine ⟨191382164307192963211736741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127588109538128642141157827 191382164307192963211736741)
  ·
    refine ⟨35884155807598680602200639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 191382164307192963211736741 35884155807598680602200639)
    ·
      refine ⟨53826233711398020903300959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35884155807598680602200639 53826233711398020903300959)
      ·
        refine ⟨80739350567097031354951439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53826233711398020903300959 80739350567097031354951439)
        ·
          refine ⟨121109025850645547032427159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80739350567097031354951439 121109025850645547032427159)
          ·
            refine ⟨181663538775968320548640739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121109025850645547032427159 181663538775968320548640739)
            ·
              refine ⟨272495308163952480822961109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181663538775968320548640739 272495308163952480822961109)
              ·
                refine ⟨6386608785092636269288151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 272495308163952480822961109 6386608785092636269288151)
                ·
                  refine ⟨9579913177638954403932227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6386608785092636269288151 9579913177638954403932227)
                  ·
                    refine ⟨14369869766458431605898341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9579913177638954403932227 14369869766458431605898341)
                    ·
                      refine ⟨2694350581210955926105939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14369869766458431605898341 2694350581210955926105939)
                      ·
                        rfl

theorem cell23_5247229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 7, 1, 1, 4].length) (baseStart_5247229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5247229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5247229 prefixEnd_5247229 := by exact prefixLift 5247229
  have htrace : WordTrace (prefixWord ++ tailWord_5247229) baseStart_5247229 baseEnd_5247229 := by
    simpa [prefixWord, tailWord_5247229, baseEnd_5247229] using wordTrace_append hprefix tailTrace_5247229
  have hstable : (prefixWord ++ tailWord_5247229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5247229).length < 2 ^ (prefixWord ++ tailWord_5247229).sum := by decide
  have hdescent : baseEnd_5247229 < baseStart_5247229 := by decide
  rcases family_descends (prefixWord ++ tailWord_5247229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5247240 : List Nat := [2, 1, 3, 2, 3, 1, 4, 2, 1, 1, 3]
def baseStart_5247240 : Nat := 118140960795 + 5247240 * 2 ^ 59
def prefixEnd_5247240 : Nat := 4983230072969 + 3 ^ 40 * 5247240 * 2
def baseEnd_5247240 : Nat := 2694356229498155383068389

theorem tailTrace_5247240 : CollatzResearch.WordTrace tailWord_5247240 prefixEnd_5247240 2694356229498155383068389 := by
  unfold tailWord_5247240
  simp only [CollatzResearch.WordTrace]
  refine ⟨95691282755076556045193587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127588377006768741393591449 95691282755076556045193587)
  ·
    refine ⟨143536924132614834067790381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95691282755076556045193587 143536924132614834067790381)
    ·
      refine ⟨53826346549730562775421393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143536924132614834067790381 53826346549730562775421393)
      ·
        refine ⟨40369759912297922081566045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53826346549730562775421393 40369759912297922081566045)
        ·
          refine ⟨15138659967111720780587267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40369759912297922081566045 15138659967111720780587267)
          ·
            refine ⟨22707989950667581170880901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15138659967111720780587267 22707989950667581170880901)
            ·
              refine ⟨4257748115750171469540169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22707989950667581170880901 4257748115750171469540169)
              ·
                refine ⟨3193311086812628602155127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4257748115750171469540169 3193311086812628602155127)
                ·
                  refine ⟨4789966630218942903232691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3193311086812628602155127 4789966630218942903232691)
                  ·
                    refine ⟨7184949945328414354849037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4789966630218942903232691 7184949945328414354849037)
                    ·
                      refine ⟨2694356229498155383068389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7184949945328414354849037 2694356229498155383068389)
                      ·
                        rfl

theorem cell23_5247240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 4, 2, 1, 1, 3].length) (baseStart_5247240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5247240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5247240 prefixEnd_5247240 := by exact prefixLift 5247240
  have htrace : WordTrace (prefixWord ++ tailWord_5247240) baseStart_5247240 baseEnd_5247240 := by
    simpa [prefixWord, tailWord_5247240, baseEnd_5247240] using wordTrace_append hprefix tailTrace_5247240
  have hstable : (prefixWord ++ tailWord_5247240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5247240).length < 2 ^ (prefixWord ++ tailWord_5247240).sum := by decide
  have hdescent : baseEnd_5247240 < baseStart_5247240 := by decide
  rcases family_descends (prefixWord ++ tailWord_5247240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5247242 : List Nat := [3, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6]
def baseStart_5247242 : Nat := 118140960795 + 5247242 * 2 ^ 59
def prefixEnd_5247242 : Nat := 4983230072969 + 3 ^ 40 * 5247242 * 2
def baseEnd_5247242 : Nat := 2694357256459464375243379

theorem tailTrace_5247242 : CollatzResearch.WordTrace tailWord_5247242 prefixEnd_5247242 2694357256459464375243379 := by
  unfold tailWord_5247242
  simp only [CollatzResearch.WordTrace]
  refine ⟨47845659614036466607989995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127588425637430577621306653 47845659614036466607989995)
  ·
    refine ⟨71768489421054699911984993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47845659614036466607989995 71768489421054699911984993)
    ·
      refine ⟨53826367065791024933988745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71768489421054699911984993 53826367065791024933988745)
      ·
        refine ⟨40369775299343268700491559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53826367065791024933988745 40369775299343268700491559)
        ·
          refine ⟨60554662949014903050737339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40369775299343268700491559 60554662949014903050737339)
          ·
            refine ⟨90831994423522354576106009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60554662949014903050737339 90831994423522354576106009)
            ·
              refine ⟨68123995817641765932079507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90831994423522354576106009 68123995817641765932079507)
              ·
                refine ⟨102185993726462648898119261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68123995817641765932079507 102185993726462648898119261)
                ·
                  refine ⟨38319747647423493336794723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102185993726462648898119261 38319747647423493336794723)
                  ·
                    refine ⟨57479621471135240005192085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38319747647423493336794723 57479621471135240005192085)
                    ·
                      refine ⟨2694357256459464375243379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57479621471135240005192085 2694357256459464375243379)
                      ·
                        rfl

theorem cell23_5247242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_5247242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5247242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5247242 prefixEnd_5247242 := by exact prefixLift 5247242
  have htrace : WordTrace (prefixWord ++ tailWord_5247242) baseStart_5247242 baseEnd_5247242 := by
    simpa [prefixWord, tailWord_5247242, baseEnd_5247242] using wordTrace_append hprefix tailTrace_5247242
  have hstable : (prefixWord ++ tailWord_5247242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5247242).length < 2 ^ (prefixWord ++ tailWord_5247242).sum := by decide
  have hdescent : baseEnd_5247242 < baseStart_5247242 := by decide
  rcases family_descends (prefixWord ++ tailWord_5247242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5247249 : List Nat := [1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 3]
def baseStart_5247249 : Nat := 118140960795 + 5247249 * 2 ^ 59
def prefixEnd_5247249 : Nat := 4983230072969 + 3 ^ 40 * 5247249 * 2
def baseEnd_5247249 : Nat := 2694360850824045847855847

theorem tailTrace_5247249 : CollatzResearch.WordTrace tailWord_5247249 prefixEnd_5247249 2694360850824045847855847 := by
  unfold tailWord_5247249
  simp only [CollatzResearch.WordTrace]
  refine ⟨191382893767120506627464801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127588595844747004418309867 191382893767120506627464801)
  ·
    refine ⟨143537170325340379970598601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191382893767120506627464801 143537170325340379970598601)
    ·
      refine ⟨107652877744005284977948951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143537170325340379970598601 107652877744005284977948951)
      ·
        refine ⟨161479316616007927466923427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107652877744005284977948951 161479316616007927466923427)
        ·
          refine ⟨242218974924011891200385141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161479316616007927466923427 242218974924011891200385141)
          ·
            refine ⟨22708028899126114800036107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 242218974924011891200385141 22708028899126114800036107)
            ·
              refine ⟨34062043348689172200054161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22708028899126114800036107 34062043348689172200054161)
              ·
                refine ⟨25546532511516879150040621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34062043348689172200054161 25546532511516879150040621)
                ·
                  refine ⟨9579949691818829681265233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25546532511516879150040621 9579949691818829681265233)
                  ·
                    refine ⟨7184962268864122260948925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9579949691818829681265233 7184962268864122260948925)
                    ·
                      refine ⟨2694360850824045847855847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7184962268864122260948925 2694360850824045847855847)
                      ·
                        rfl

theorem cell23_5247249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 3].length) (baseStart_5247249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5247249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5247249 prefixEnd_5247249 := by exact prefixLift 5247249
  have htrace : WordTrace (prefixWord ++ tailWord_5247249) baseStart_5247249 baseEnd_5247249 := by
    simpa [prefixWord, tailWord_5247249, baseEnd_5247249] using wordTrace_append hprefix tailTrace_5247249
  have hstable : (prefixWord ++ tailWord_5247249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5247249).length < 2 ^ (prefixWord ++ tailWord_5247249).sum := by decide
  have hdescent : baseEnd_5247249 < baseStart_5247249 := by decide
  rcases family_descends (prefixWord ++ tailWord_5247249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5247263 : List Nat := [1, 1, 2, 4, 3, 2, 1, 2, 3, 2, 2]
def baseStart_5247263 : Nat := 118140960795 + 5247263 * 2 ^ 59
def prefixEnd_5247263 : Nat := 4983230072969 + 3 ^ 40 * 5247263 * 2
def baseEnd_5247263 : Nat := 2694368039553208793080783

theorem tailTrace_5247263 : CollatzResearch.WordTrace tailWord_5247263 prefixEnd_5247263 2694368039553208793080783 := by
  unfold tailWord_5247263
  simp only [CollatzResearch.WordTrace]
  refine ⟨191383404389069787018474443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127588936259379858012316295 191383404389069787018474443)
  ·
    refine ⟨287075106583604680527711665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191383404389069787018474443 287075106583604680527711665)
    ·
      refine ⟨215306329937703510395783749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287075106583604680527711665 215306329937703510395783749)
      ·
        refine ⟨40369936863319408199209453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 215306329937703510395783749 40369936863319408199209453)
        ·
          refine ⟨15138726323744778074703545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40369936863319408199209453 15138726323744778074703545)
          ·
            refine ⟨11354044742808583556027659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15138726323744778074703545 11354044742808583556027659)
            ·
              refine ⟨17031067114212875334041489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11354044742808583556027659 17031067114212875334041489)
              ·
                refine ⟨12773300335659656500531117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17031067114212875334041489 12773300335659656500531117)
                ·
                  refine ⟨4789987625872371187699169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12773300335659656500531117 4789987625872371187699169)
                  ·
                    refine ⟨3592490719404278390774377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4789987625872371187699169 3592490719404278390774377)
                    ·
                      refine ⟨2694368039553208793080783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3592490719404278390774377 2694368039553208793080783)
                      ·
                        rfl

theorem cell23_5247263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 2, 3, 2, 2].length) (baseStart_5247263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5247263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5247263 prefixEnd_5247263 := by exact prefixLift 5247263
  have htrace : WordTrace (prefixWord ++ tailWord_5247263) baseStart_5247263 baseEnd_5247263 := by
    simpa [prefixWord, tailWord_5247263, baseEnd_5247263] using wordTrace_append hprefix tailTrace_5247263
  have hstable : (prefixWord ++ tailWord_5247263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5247263).length < 2 ^ (prefixWord ++ tailWord_5247263).sum := by decide
  have hdescent : baseEnd_5247263 < baseStart_5247263 := by decide
  rcases family_descends (prefixWord ++ tailWord_5247263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5247266 : List Nat := [3, 3, 1, 1, 3, 1, 2, 1, 3, 2, 3]
def baseStart_5247266 : Nat := 118140960795 + 5247266 * 2 ^ 59
def prefixEnd_5247266 : Nat := 4983230072969 + 3 ^ 40 * 5247266 * 2
def baseEnd_5247266 : Nat := 2694369579995172281343269

theorem tailTrace_5247266 : CollatzResearch.WordTrace tailWord_5247266 prefixEnd_5247266 2694369579995172281343269 := by
  unfold tailWord_5247266
  simp only [CollatzResearch.WordTrace]
  refine ⟨47845878452014729632708413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127589009205372612353889101 47845878452014729632708413)
  ·
    refine ⟨17942204419505523612265655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47845878452014729632708413 17942204419505523612265655)
    ·
      refine ⟨26913306629258285418398483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17942204419505523612265655 26913306629258285418398483)
      ·
        refine ⟨40369959943887428127597725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26913306629258285418398483 40369959943887428127597725)
        ·
          refine ⟨15138734978957785547849147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40369959943887428127597725 15138734978957785547849147)
          ·
            refine ⟨22708102468436678321773721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15138734978957785547849147 22708102468436678321773721)
            ·
              refine ⟨17031076851327508741330291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22708102468436678321773721 17031076851327508741330291)
              ·
                refine ⟨25546615276991263111995437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17031076851327508741330291 25546615276991263111995437)
                ·
                  refine ⟨9579980728871723666998289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25546615276991263111995437 9579980728871723666998289)
                  ·
                    refine ⟨7184985546653792750248717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9579980728871723666998289 7184985546653792750248717)
                    ·
                      refine ⟨2694369579995172281343269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7184985546653792750248717 2694369579995172281343269)
                      ·
                        rfl

theorem cell23_5247266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_5247266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5247266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5247266 prefixEnd_5247266 := by exact prefixLift 5247266
  have htrace : WordTrace (prefixWord ++ tailWord_5247266) baseStart_5247266 baseEnd_5247266 := by
    simpa [prefixWord, tailWord_5247266, baseEnd_5247266] using wordTrace_append hprefix tailTrace_5247266
  have hstable : (prefixWord ++ tailWord_5247266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5247266).length < 2 ^ (prefixWord ++ tailWord_5247266).sum := by decide
  have hdescent : baseEnd_5247266 < baseStart_5247266 := by decide
  rcases family_descends (prefixWord ++ tailWord_5247266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5247277 : List Nat := [1, 5, 3, 1, 3, 1, 2, 1, 1, 5]
def baseStart_5247277 : Nat := 118140960795 + 5247277 * 2 ^ 59
def prefixEnd_5247277 : Nat := 4983230072969 + 3 ^ 40 * 5247277 * 2
def baseEnd_5247277 : Nat := 898125076094123912768573

theorem tailTrace_5247277 : CollatzResearch.WordTrace tailWord_5247277 prefixEnd_5247277 898125076094123912768573 := by
  unfold tailWord_5247277
  simp only [CollatzResearch.WordTrace]
  refine ⟨191383915011019067409484085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127589276674012711606322723 191383915011019067409484085)
  ·
    refine ⟨17942242032283037569639133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 191383915011019067409484085 17942242032283037569639133)
    ·
      refine ⟨6728340762106139088614675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17942242032283037569639133 6728340762106139088614675)
      ·
        refine ⟨10092511143159208632922013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6728340762106139088614675 10092511143159208632922013)
        ·
          refine ⟨3784691678684703237345755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10092511143159208632922013 3784691678684703237345755)
          ·
            refine ⟨5677037518027054856018633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3784691678684703237345755 5677037518027054856018633)
            ·
              refine ⟨4257778138520291142013975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5677037518027054856018633 4257778138520291142013975)
              ·
                refine ⟨6386667207780436713020963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4257778138520291142013975 6386667207780436713020963)
                ·
                  refine ⟨9580000811670655069531445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6386667207780436713020963 9580000811670655069531445)
                  ·
                    refine ⟨898125076094123912768573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9580000811670655069531445 898125076094123912768573)
                    ·
                      rfl

theorem cell23_5247277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_5247277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5247277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5247277 prefixEnd_5247277 := by exact prefixLift 5247277
  have htrace : WordTrace (prefixWord ++ tailWord_5247277) baseStart_5247277 baseEnd_5247277 := by
    simpa [prefixWord, tailWord_5247277, baseEnd_5247277] using wordTrace_append hprefix tailTrace_5247277
  have hstable : (prefixWord ++ tailWord_5247277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5247277).length < 2 ^ (prefixWord ++ tailWord_5247277).sum := by decide
  have hdescent : baseEnd_5247277 < baseStart_5247277 := by decide
  rcases family_descends (prefixWord ++ tailWord_5247277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5247279 : List Nat := [1, 1, 2, 1, 2, 1, 6, 2, 1, 3, 3]
def baseStart_5247279 : Nat := 118140960795 + 5247279 * 2 ^ 59
def prefixEnd_5247279 : Nat := 4983230072969 + 3 ^ 40 * 5247279 * 2
def baseEnd_5247279 : Nat := 2694376255243680730480709

theorem tailTrace_5247279 : CollatzResearch.WordTrace tailWord_5247279 prefixEnd_5247279 2694376255243680730480709 := by
  unfold tailWord_5247279
  simp only [CollatzResearch.WordTrace]
  refine ⟨191383987957011821751056891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127589325304674547834037927 191383987957011821751056891)
  ·
    refine ⟨287075981935517732626585337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191383987957011821751056891 287075981935517732626585337)
    ·
      refine ⟨215306986451638299469939003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287075981935517732626585337 215306986451638299469939003)
      ·
        refine ⟨322960479677457449204908505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215306986451638299469939003 322960479677457449204908505)
        ·
          refine ⟨242220359758093086903681379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 322960479677457449204908505 242220359758093086903681379)
          ·
            refine ⟨363330539637139630355522069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242220359758093086903681379 363330539637139630355522069)
            ·
              refine ⟨17031119045490920172915097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 363330539637139630355522069 17031119045490920172915097)
              ·
                refine ⟨12773339284118190129686323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17031119045490920172915097 12773339284118190129686323)
                ·
                  refine ⟨19160008926177285194529485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12773339284118190129686323 19160008926177285194529485)
                  ·
                    refine ⟨7185003347316481947948557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19160008926177285194529485 7185003347316481947948557)
                    ·
                      refine ⟨2694376255243680730480709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7185003347316481947948557 2694376255243680730480709)
                      ·
                        rfl

theorem cell23_5247279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 2, 1, 3, 3].length) (baseStart_5247279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5247279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5247279 prefixEnd_5247279 := by exact prefixLift 5247279
  have htrace : WordTrace (prefixWord ++ tailWord_5247279) baseStart_5247279 baseEnd_5247279 := by
    simpa [prefixWord, tailWord_5247279, baseEnd_5247279] using wordTrace_append hprefix tailTrace_5247279
  have hstable : (prefixWord ++ tailWord_5247279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5247279).length < 2 ^ (prefixWord ++ tailWord_5247279).sum := by decide
  have hdescent : baseEnd_5247279 < baseStart_5247279 := by decide
  rcases family_descends (prefixWord ++ tailWord_5247279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5247296 : List Nat := [2, 1, 1, 2, 2, 1, 2, 6, 2, 1, 3]
def baseStart_5247296 : Nat := 118140960795 + 5247296 * 2 ^ 59
def prefixEnd_5247296 : Nat := 4983230072969 + 3 ^ 40 * 5247296 * 2
def baseEnd_5247296 : Nat := 2694384984414807163968131

theorem tailTrace_5247296 : CollatzResearch.WordTrace tailWord_5247296 prefixEnd_5247296 2694384984414807163968131 := by
  unfold tailWord_5247296
  simp only [CollatzResearch.WordTrace]
  refine ⟨95692303998975116827212871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127589738665300155769617161 95692303998975116827212871)
  ·
    refine ⟨143538455998462675240819307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95692303998975116827212871 143538455998462675240819307)
    ·
      refine ⟨215307683997694012861228961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143538455998462675240819307 215307683997694012861228961)
      ·
        refine ⟨161480762998270509645921721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215307683997694012861228961 161480762998270509645921721)
        ·
          refine ⟨121110572248702882234441291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161480762998270509645921721 121110572248702882234441291)
          ·
            refine ⟨181665858373054323351661937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121110572248702882234441291 181665858373054323351661937)
            ·
              refine ⟨136249393779790742513746453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 181665858373054323351661937 136249393779790742513746453)
              ·
                refine ⟨6386690333427691055331865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 136249393779790742513746453 6386690333427691055331865)
                ·
                  refine ⟨4790017750070768291498899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6386690333427691055331865 4790017750070768291498899)
                  ·
                    refine ⟨7185026625106152437248349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4790017750070768291498899 7185026625106152437248349)
                    ·
                      refine ⟨2694384984414807163968131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7185026625106152437248349 2694384984414807163968131)
                      ·
                        rfl

theorem cell23_5247296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 6, 2, 1, 3].length) (baseStart_5247296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5247296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5247296 prefixEnd_5247296 := by exact prefixLift 5247296
  have htrace : WordTrace (prefixWord ++ tailWord_5247296) baseStart_5247296 baseEnd_5247296 := by
    simpa [prefixWord, tailWord_5247296, baseEnd_5247296] using wordTrace_append hprefix tailTrace_5247296
  have hstable : (prefixWord ++ tailWord_5247296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5247296).length < 2 ^ (prefixWord ++ tailWord_5247296).sum := by decide
  have hdescent : baseEnd_5247296 < baseStart_5247296 := by decide
  rcases family_descends (prefixWord ++ tailWord_5247296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5247353 : List Nat := [1, 2, 1, 3, 2, 1, 1, 6, 2, 2, 2]
def baseStart_5247353 : Nat := 118140960795 + 5247353 * 2 ^ 59
def prefixEnd_5247353 : Nat := 4983230072969 + 3 ^ 40 * 5247353 * 2
def baseEnd_5247353 : Nat := 2694414252812113440955369

theorem tailTrace_5247353 : CollatzResearch.WordTrace tailWord_5247353 prefixEnd_5247353 2694414252812113440955369 := by
  unfold tailWord_5247353
  simp only [CollatzResearch.WordTrace]
  refine ⟨191386686958743732389250713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127591124639162488259500475 191386686958743732389250713)
  ·
    refine ⟨143540015219057799291938035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191386686958743732389250713 143540015219057799291938035)
    ·
      refine ⟨215310022828586698937907053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143540015219057799291938035 215310022828586698937907053)
      ·
        refine ⟨80741258560720012101715145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 215310022828586698937907053 80741258560720012101715145)
        ·
          refine ⟨60555943920540009076286359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80741258560720012101715145 60555943920540009076286359)
          ·
            refine ⟨90833915880810013614429539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60555943920540009076286359 90833915880810013614429539)
            ·
              refine ⟨136250873821215020421644309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90833915880810013614429539 136250873821215020421644309)
              ·
                refine ⟨6386759710369454082264577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 136250873821215020421644309 6386759710369454082264577)
                ·
                  refine ⟨4790069782777090561698433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6386759710369454082264577 4790069782777090561698433)
                  ·
                    refine ⟨3592552337082817921273825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4790069782777090561698433 3592552337082817921273825)
                    ·
                      refine ⟨2694414252812113440955369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3592552337082817921273825 2694414252812113440955369)
                      ·
                        rfl

theorem cell23_5247353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 6, 2, 2, 2].length) (baseStart_5247353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5247353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5247353 prefixEnd_5247353 := by exact prefixLift 5247353
  have htrace : WordTrace (prefixWord ++ tailWord_5247353) baseStart_5247353 baseEnd_5247353 := by
    simpa [prefixWord, tailWord_5247353, baseEnd_5247353] using wordTrace_append hprefix tailTrace_5247353
  have hstable : (prefixWord ++ tailWord_5247353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5247353).length < 2 ^ (prefixWord ++ tailWord_5247353).sum := by decide
  have hdescent : baseEnd_5247353 < baseStart_5247353 := by decide
  rcases family_descends (prefixWord ++ tailWord_5247353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5247449 : List Nat := [1, 2, 1, 2, 4, 1, 2, 2, 8]
def baseStart_5247449 : Nat := 118140960795 + 5247449 * 2 ^ 59
def prefixEnd_5247449 : Nat := 4983230072969 + 3 ^ 40 * 5247449 * 2
def baseEnd_5247449 : Nat := 299384838550549451706103

theorem tailTrace_5247449 : CollatzResearch.WordTrace tailWord_5247449 prefixEnd_5247449 299384838550549451706103 := by
  unfold tailWord_5247449
  simp only [CollatzResearch.WordTrace]
  refine ⟨191390188366395940784745401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127593458910930627189830267 191390188366395940784745401)
  ·
    refine ⟨143542641274796955588559051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191390188366395940784745401 143542641274796955588559051)
    ·
      refine ⟨215313961912195433382838577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143542641274796955588559051 215313961912195433382838577)
      ·
        refine ⟨161485471434146575037128933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215313961912195433382838577 161485471434146575037128933)
        ·
          refine ⟨30278525893902482819461675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 161485471434146575037128933 30278525893902482819461675)
          ·
            refine ⟨45417788840853724229192513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30278525893902482819461675 45417788840853724229192513)
            ·
              refine ⟨34063341630640293171894385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45417788840853724229192513 34063341630640293171894385)
              ·
                refine ⟨25547506222980219878920789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34063341630640293171894385 25547506222980219878920789)
                ·
                  refine ⟨299384838550549451706103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25547506222980219878920789 299384838550549451706103)
                  ·
                    rfl

theorem cell23_5247449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 8].length) (baseStart_5247449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5247449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5247449 prefixEnd_5247449 := by exact prefixLift 5247449
  have htrace : WordTrace (prefixWord ++ tailWord_5247449) baseStart_5247449 baseEnd_5247449 := by
    simpa [prefixWord, tailWord_5247449, baseEnd_5247449] using wordTrace_append hprefix tailTrace_5247449
  have hstable : (prefixWord ++ tailWord_5247449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5247449).length < 2 ^ (prefixWord ++ tailWord_5247449).sum := by decide
  have hdescent : baseEnd_5247449 < baseStart_5247449 := by decide
  rcases family_descends (prefixWord ++ tailWord_5247449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5247466 : List Nat := [3, 1, 3, 1, 3, 2, 1, 1, 8]
def baseStart_5247466 : Nat := 118140960795 + 5247466 * 2 ^ 59
def prefixEnd_5247466 : Nat := 4983230072969 + 3 ^ 40 * 5247466 * 2
def baseEnd_5247466 : Nat := 299385808458452388760261

theorem tailTrace_5247466 : CollatzResearch.WordTrace tailWord_5247466 prefixEnd_5247466 299385808458452388760261 := by
  unfold tailWord_5247466
  simp only [CollatzResearch.WordTrace]
  refine ⟨47847702101833588172028563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127593872271556235125409501 47847702101833588172028563)
  ·
    refine ⟨71771553152750382258042845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47847702101833588172028563 71771553152750382258042845)
    ·
      refine ⟨26914332432281393346766067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71771553152750382258042845 26914332432281393346766067)
      ·
        refine ⟨40371498648422090020149101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26914332432281393346766067 40371498648422090020149101)
        ·
          refine ⟨15139311993158283757555913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40371498648422090020149101 15139311993158283757555913)
          ·
            refine ⟨11354483994868712818166935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15139311993158283757555913 11354483994868712818166935)
            ·
              refine ⟨17031725992303069227250403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11354483994868712818166935 17031725992303069227250403)
              ·
                refine ⟨25547588988454603840875605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17031725992303069227250403 25547588988454603840875605)
                ·
                  refine ⟨299385808458452388760261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25547588988454603840875605 299385808458452388760261)
                  ·
                    rfl

theorem cell23_5247466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 8].length) (baseStart_5247466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5247466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5247466 prefixEnd_5247466 := by exact prefixLift 5247466
  have htrace : WordTrace (prefixWord ++ tailWord_5247466) baseStart_5247466 baseEnd_5247466 := by
    simpa [prefixWord, tailWord_5247466, baseEnd_5247466] using wordTrace_append hprefix tailTrace_5247466
  have hstable : (prefixWord ++ tailWord_5247466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5247466).length < 2 ^ (prefixWord ++ tailWord_5247466).sum := by decide
  have hdescent : baseEnd_5247466 < baseStart_5247466 := by decide
  rcases family_descends (prefixWord ++ tailWord_5247466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5247470 : List Nat := [4, 1, 2, 1, 2, 2, 2, 4, 1, 4]
def baseStart_5247470 : Nat := 118140960795 + 5247470 * 2 ^ 59
def prefixEnd_5247470 : Nat := 4983230072969 + 3 ^ 40 * 5247470 * 2
def baseEnd_5247470 : Nat := 898158110016229827730777

theorem tailTrace_5247470 : CollatzResearch.WordTrace tailWord_5247470 prefixEnd_5247470 898158110016229827730777 := by
  unfold tailWord_5247470
  simp only [CollatzResearch.WordTrace]
  refine ⟨23923869287414982671407483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127593969532879907580839909 23923869287414982671407483)
  ·
    refine ⟨35885803931122474007111225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23923869287414982671407483 35885803931122474007111225)
    ·
      refine ⟨26914352948341855505333419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35885803931122474007111225 26914352948341855505333419)
      ·
        refine ⟨40371529422512783258000129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26914352948341855505333419 40371529422512783258000129)
        ·
          refine ⟨30278647066884587443500097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40371529422512783258000129 30278647066884587443500097)
          ·
            refine ⟨22708985300163440582625073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30278647066884587443500097 22708985300163440582625073)
            ·
              refine ⟨17031738975122580436968805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22708985300163440582625073 17031738975122580436968805)
              ·
                refine ⟨3193451057835483831931651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17031738975122580436968805 3193451057835483831931651)
                ·
                  refine ⟨4790176586753225747897477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3193451057835483831931651 4790176586753225747897477)
                  ·
                    refine ⟨898158110016229827730777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4790176586753225747897477 898158110016229827730777)
                    ·
                      rfl

theorem cell23_5247470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 4, 1, 4].length) (baseStart_5247470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5247470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5247470 prefixEnd_5247470 := by exact prefixLift 5247470
  have htrace : WordTrace (prefixWord ++ tailWord_5247470) baseStart_5247470 baseEnd_5247470 := by
    simpa [prefixWord, tailWord_5247470, baseEnd_5247470] using wordTrace_append hprefix tailTrace_5247470
  have hstable : (prefixWord ++ tailWord_5247470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5247470).length < 2 ^ (prefixWord ++ tailWord_5247470).sum := by decide
  have hdescent : baseEnd_5247470 < baseStart_5247470 := by decide
  rcases family_descends (prefixWord ++ tailWord_5247470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5247493 : List Nat := [1, 3, 1, 1, 2, 2, 4, 2, 3, 1, 3]
def baseStart_5247493 : Nat := 118140960795 + 5247493 * 2 ^ 59
def prefixEnd_5247493 : Nat := 4983230072969 + 3 ^ 40 * 5247493 * 2
def baseEnd_5247493 : Nat := 2694486140103742893204725

theorem tailTrace_5247493 : CollatzResearch.WordTrace tailWord_5247493 prefixEnd_5247493 2694486140103742893204725 := by
  unfold tailWord_5247493
  simp only [CollatzResearch.WordTrace]
  refine ⟨191391793178236536299347133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127594528785491024199564755 191391793178236536299347133)
  ·
    refine ⟨71771922441838701112255175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191391793178236536299347133 71771922441838701112255175)
    ·
      refine ⟨107657883662758051668382763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71771922441838701112255175 107657883662758051668382763)
      ·
        refine ⟨161486825494137077502574145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107657883662758051668382763 161486825494137077502574145)
        ·
          refine ⟨121115119120602808126930609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161486825494137077502574145 121115119120602808126930609)
          ·
            refine ⟨90836339340452106095197957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121115119120602808126930609 90836339340452106095197957)
            ·
              refine ⟨17031813626334769892849617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90836339340452106095197957 17031813626334769892849617)
              ·
                refine ⟨12773860219751077419637213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17031813626334769892849617 12773860219751077419637213)
                ·
                  refine ⟨4790197582406654032363955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12773860219751077419637213 4790197582406654032363955)
                  ·
                    refine ⟨7185296373609981048545933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4790197582406654032363955 7185296373609981048545933)
                    ·
                      refine ⟨2694486140103742893204725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7185296373609981048545933 2694486140103742893204725)
                      ·
                        rfl

theorem cell23_5247493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 2, 3, 1, 3].length) (baseStart_5247493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5247493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5247493 prefixEnd_5247493 := by exact prefixLift 5247493
  have htrace : WordTrace (prefixWord ++ tailWord_5247493) baseStart_5247493 baseEnd_5247493 := by
    simpa [prefixWord, tailWord_5247493, baseEnd_5247493] using wordTrace_append hprefix tailTrace_5247493
  have hstable : (prefixWord ++ tailWord_5247493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5247493).length < 2 ^ (prefixWord ++ tailWord_5247493).sum := by decide
  have hdescent : baseEnd_5247493 < baseStart_5247493 := by decide
  rcases family_descends (prefixWord ++ tailWord_5247493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5247536 : List Nat := [2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 5]
def baseStart_5247536 : Nat := 118140960795 + 5247536 * 2 ^ 59
def prefixEnd_5247536 : Nat := 4983230072969 + 3 ^ 40 * 5247536 * 2
def baseEnd_5247536 : Nat := 2694508219771886224967027

theorem tailTrace_5247536 : CollatzResearch.WordTrace tailWord_5247536 prefixEnd_5247536 2694508219771886224967027 := by
  unfold tailWord_5247536
  simp only [CollatzResearch.WordTrace]
  refine ⟨95696680758540377321581231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127595574344720503095441641 95696680758540377321581231)
  ·
    refine ⟨143545021137810565982371847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95696680758540377321581231 143545021137810565982371847)
    ·
      refine ⟨215317531706715848973557771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143545021137810565982371847 215317531706715848973557771)
      ·
        refine ⟨322976297560073773460336657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215317531706715848973557771 322976297560073773460336657)
        ·
          refine ⟨242232223170055330095252493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 322976297560073773460336657 242232223170055330095252493)
          ·
            refine ⟨90837083688770748785719685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 242232223170055330095252493 90837083688770748785719685)
            ·
              refine ⟨17031953191644515397322441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90837083688770748785719685 17031953191644515397322441)
              ·
                refine ⟨12773964893733386547991831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17031953191644515397322441 12773964893733386547991831)
                ·
                  refine ⟨19160947340600079821987747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12773964893733386547991831 19160947340600079821987747)
                  ·
                    refine ⟨28741421010900119732981621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19160947340600079821987747 28741421010900119732981621)
                    ·
                      refine ⟨2694508219771886224967027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28741421010900119732981621 2694508219771886224967027)
                      ·
                        rfl

theorem cell23_5247536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 5].length) (baseStart_5247536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5247536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5247536 prefixEnd_5247536 := by exact prefixLift 5247536
  have htrace : WordTrace (prefixWord ++ tailWord_5247536) baseStart_5247536 baseEnd_5247536 := by
    simpa [prefixWord, tailWord_5247536, baseEnd_5247536] using wordTrace_append hprefix tailTrace_5247536
  have hstable : (prefixWord ++ tailWord_5247536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5247536).length < 2 ^ (prefixWord ++ tailWord_5247536).sum := by decide
  have hdescent : baseEnd_5247536 < baseStart_5247536 := by decide
  rcases family_descends (prefixWord ++ tailWord_5247536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5247543 : List Nat := [1, 1, 3, 1, 2, 3, 3, 3, 2, 4]
def baseStart_5247543 : Nat := 118140960795 + 5247543 * 2 ^ 59
def prefixEnd_5247543 : Nat := 4983230072969 + 3 ^ 40 * 5247543 * 2
def baseEnd_5247543 : Nat := 898170604712155899193165

theorem tailTrace_5247543 : CollatzResearch.WordTrace tailWord_5247543 prefixEnd_5247543 898170604712155899193165 := by
  unfold tailWord_5247543
  simp only [CollatzResearch.WordTrace]
  refine ⟨191393616828055394838667283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127595744552036929892444855 191393616828055394838667283)
  ·
    refine ⟨287090425242083092258000925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191393616828055394838667283 287090425242083092258000925)
    ·
      refine ⟨107658909465781159596750347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 287090425242083092258000925 107658909465781159596750347)
      ·
        refine ⟨161488364198671739395125521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107658909465781159596750347 161488364198671739395125521)
        ·
          refine ⟨121116273149003804546344141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161488364198671739395125521 121116273149003804546344141)
          ·
            refine ⟨45418602430876426704879053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121116273149003804546344141 45418602430876426704879053)
            ·
              refine ⟨17031975911578660014329645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45418602430876426704879053 17031975911578660014329645)
              ·
                refine ⟨6386990966841997505373617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17031975911578660014329645 6386990966841997505373617)
                ·
                  refine ⟨4790243225131498129030213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6386990966841997505373617 4790243225131498129030213)
                  ·
                    refine ⟨898170604712155899193165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4790243225131498129030213 898170604712155899193165)
                    ·
                      rfl

theorem cell23_5247543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 3, 2, 4].length) (baseStart_5247543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5247543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5247543 prefixEnd_5247543 := by exact prefixLift 5247543
  have htrace : WordTrace (prefixWord ++ tailWord_5247543) baseStart_5247543 baseEnd_5247543 := by
    simpa [prefixWord, tailWord_5247543, baseEnd_5247543] using wordTrace_append hprefix tailTrace_5247543
  have hstable : (prefixWord ++ tailWord_5247543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5247543).length < 2 ^ (prefixWord ++ tailWord_5247543).sum := by decide
  have hdescent : baseEnd_5247543 < baseStart_5247543 := by decide
  rcases family_descends (prefixWord ++ tailWord_5247543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5247546 : List Nat := [3, 1, 1, 1, 3, 3, 2, 1, 1, 1, 6]
def baseStart_5247546 : Nat := 118140960795 + 5247546 * 2 ^ 59
def prefixEnd_5247546 : Nat := 4983230072969 + 3 ^ 40 * 5247546 * 2
def baseEnd_5247546 : Nat := 2694513354578431185841981

theorem tailTrace_5247546 : CollatzResearch.WordTrace tailWord_5247546 prefixEnd_5247546 2694513354578431185841981 := by
  unfold tailWord_5247546
  simp only [CollatzResearch.WordTrace]
  refine ⟨47848431561761131587756623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127595817498029684234017661 47848431561761131587756623)
  ·
    refine ⟨71772647342641697381634935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47848431561761131587756623 71772647342641697381634935)
    ·
      refine ⟨107658971013962546072452403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71772647342641697381634935 107658971013962546072452403)
      ·
        refine ⟨161488456520943819108678605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107658971013962546072452403 161488456520943819108678605)
        ·
          refine ⟨60558171195353932165754477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161488456520943819108678605 60558171195353932165754477)
          ·
            refine ⟨22709314198257724562157929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60558171195353932165754477 22709314198257724562157929)
            ·
              refine ⟨17031985648693293421618447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22709314198257724562157929 17031985648693293421618447)
              ·
                refine ⟨25547978473039940132427671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17031985648693293421618447 25547978473039940132427671)
                ·
                  refine ⟨38321967709559910198641507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25547978473039940132427671 38321967709559910198641507)
                  ·
                    refine ⟨57482951564339865297962261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38321967709559910198641507 57482951564339865297962261)
                    ·
                      refine ⟨2694513354578431185841981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57482951564339865297962261 2694513354578431185841981)
                      ·
                        rfl

theorem cell23_5247546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 1, 1, 6].length) (baseStart_5247546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5247546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5247546 prefixEnd_5247546 := by exact prefixLift 5247546
  have htrace : WordTrace (prefixWord ++ tailWord_5247546) baseStart_5247546 baseEnd_5247546 := by
    simpa [prefixWord, tailWord_5247546, baseEnd_5247546] using wordTrace_append hprefix tailTrace_5247546
  have hstable : (prefixWord ++ tailWord_5247546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5247546).length < 2 ^ (prefixWord ++ tailWord_5247546).sum := by decide
  have hdescent : baseEnd_5247546 < baseStart_5247546 := by decide
  rcases family_descends (prefixWord ++ tailWord_5247546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5247583 : List Nat := [1, 1, 2, 3, 1, 1, 1, 5, 4, 1, 3]
def baseStart_5247583 : Nat := 118140960795 + 5247583 * 2 ^ 59
def prefixEnd_5247583 : Nat := 4983230072969 + 3 ^ 40 * 5247583 * 2
def baseEnd_5247583 : Nat := 2694532353362647541079311

theorem tailTrace_5247583 : CollatzResearch.WordTrace tailWord_5247583 prefixEnd_5247583 2694532353362647541079311 := by
  unfold tailWord_5247583
  simp only [CollatzResearch.WordTrace]
  refine ⟨191395075747910481670123403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127596717165273654446748935 191395075747910481670123403)
  ·
    refine ⟨287092613621865722505185105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191395075747910481670123403 287092613621865722505185105)
    ·
      refine ⟨215319460216399291878888829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287092613621865722505185105 215319460216399291878888829)
      ·
        refine ⟨80744797581149734454583311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 215319460216399291878888829 80744797581149734454583311)
        ·
          refine ⟨121117196371724601681874967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80744797581149734454583311 121117196371724601681874967)
          ·
            refine ⟨181675794557586902522812451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121117196371724601681874967 181675794557586902522812451)
            ·
              refine ⟨272513691836380353784218677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181675794557586902522812451 272513691836380353784218677)
              ·
                refine ⟨25548158609660658167270501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 272513691836380353784218677 25548158609660658167270501)
                ·
                  refine ⟨4790279739311373406363219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25548158609660658167270501 4790279739311373406363219)
                  ·
                    refine ⟨7185419608967060109544829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4790279739311373406363219 7185419608967060109544829)
                    ·
                      refine ⟨2694532353362647541079311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7185419608967060109544829 2694532353362647541079311)
                      ·
                        rfl

theorem cell23_5247583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 4, 1, 3].length) (baseStart_5247583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5247583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5247583 prefixEnd_5247583 := by exact prefixLift 5247583
  have htrace : WordTrace (prefixWord ++ tailWord_5247583) baseStart_5247583 baseEnd_5247583 := by
    simpa [prefixWord, tailWord_5247583, baseEnd_5247583] using wordTrace_append hprefix tailTrace_5247583
  have hstable : (prefixWord ++ tailWord_5247583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5247583).length < 2 ^ (prefixWord ++ tailWord_5247583).sum := by decide
  have hdescent : baseEnd_5247583 < baseStart_5247583 := by decide
  rcases family_descends (prefixWord ++ tailWord_5247583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5247584 : List Nat := [2, 1, 1, 3, 2, 1, 6, 2, 1, 2, 2]
def baseStart_5247584 : Nat := 118140960795 + 5247584 * 2 ^ 59
def prefixEnd_5247584 : Nat := 4983230072969 + 3 ^ 40 * 5247584 * 2
def baseEnd_5247584 : Nat := 2694532866843302037166807

theorem tailTrace_5247584 : CollatzResearch.WordTrace tailWord_5247584 prefixEnd_5247584 2694532866843302037166807 := by
  unfold tailWord_5247584
  simp only [CollatzResearch.WordTrace]
  refine ⟨95697556110453429420454903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127596741480604572560606537 95697556110453429420454903)
  ·
    refine ⟨143546334165680144130682355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95697556110453429420454903 143546334165680144130682355)
    ·
      refine ⟨215319501248520216196023533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143546334165680144130682355 215319501248520216196023533)
      ·
        refine ⟨80744812968195081073508825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 215319501248520216196023533 80744812968195081073508825)
        ·
          refine ⟨60558609726146310805131619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80744812968195081073508825 60558609726146310805131619)
          ·
            refine ⟨90837914589219466207697429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60558609726146310805131619 90837914589219466207697429)
            ·
              refine ⟨4258027246369662478485817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 90837914589219466207697429 4258027246369662478485817)
              ·
                refine ⟨3193520434777246858864363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4258027246369662478485817 3193520434777246858864363)
                ·
                  refine ⟨4790280652165870288296545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3193520434777246858864363 4790280652165870288296545)
                  ·
                    refine ⟨3592710489124402716222409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4790280652165870288296545 3592710489124402716222409)
                    ·
                      refine ⟨2694532866843302037166807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3592710489124402716222409 2694532866843302037166807)
                      ·
                        rfl

theorem cell23_5247584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6, 2, 1, 2, 2].length) (baseStart_5247584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5247584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5247584 prefixEnd_5247584 := by exact prefixLift 5247584
  have htrace : WordTrace (prefixWord ++ tailWord_5247584) baseStart_5247584 baseEnd_5247584 := by
    simpa [prefixWord, tailWord_5247584, baseEnd_5247584] using wordTrace_append hprefix tailTrace_5247584
  have hstable : (prefixWord ++ tailWord_5247584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5247584).length < 2 ^ (prefixWord ++ tailWord_5247584).sum := by decide
  have hdescent : baseEnd_5247584 < baseStart_5247584 := by decide
  rcases family_descends (prefixWord ++ tailWord_5247584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5247600 : List Nat := [2, 1, 1, 1, 7, 1, 2, 1, 1, 3, 3]
def baseStart_5247600 : Nat := 118140960795 + 5247600 * 2 ^ 59
def prefixEnd_5247600 : Nat := 4983230072969 + 3 ^ 40 * 5247600 * 2
def baseEnd_5247600 : Nat := 2694541082533773974566733

theorem tailTrace_5247600 : CollatzResearch.WordTrace tailWord_5247600 prefixEnd_5247600 2694541082533773974566733 := by
  unfold tailWord_5247600
  simp only [CollatzResearch.WordTrace]
  refine ⟨95697847894424446786746127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127597130525899262382328169 95697847894424446786746127)
  ·
    refine ⟨143546771841636670180119191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95697847894424446786746127 143546771841636670180119191)
    ·
      refine ⟨215320157762455005270178787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143546771841636670180119191 215320157762455005270178787)
      ·
        refine ⟨322980236643682507905268181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215320157762455005270178787 322980236643682507905268181)
        ·
          refine ⟨7569849296336308779029723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 322980236643682507905268181 7569849296336308779029723)
          ·
            refine ⟨11354773944504463168544585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7569849296336308779029723 11354773944504463168544585)
            ·
              refine ⟨8516080458378347376408439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11354773944504463168544585 8516080458378347376408439)
              ·
                refine ⟨12774120687567521064612659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8516080458378347376408439 12774120687567521064612659)
                ·
                  refine ⟨19161181031351281596918989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12774120687567521064612659 19161181031351281596918989)
                  ·
                    refine ⟨7185442886756730598844621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19161181031351281596918989 7185442886756730598844621)
                    ·
                      refine ⟨2694541082533773974566733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7185442886756730598844621 2694541082533773974566733)
                      ·
                        rfl

theorem cell23_5247600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 1, 1, 3, 3].length) (baseStart_5247600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5247600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5247600 prefixEnd_5247600 := by exact prefixLift 5247600
  have htrace : WordTrace (prefixWord ++ tailWord_5247600) baseStart_5247600 baseEnd_5247600 := by
    simpa [prefixWord, tailWord_5247600, baseEnd_5247600] using wordTrace_append hprefix tailTrace_5247600
  have hstable : (prefixWord ++ tailWord_5247600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5247600).length < 2 ^ (prefixWord ++ tailWord_5247600).sum := by decide
  have hdescent : baseEnd_5247600 < baseStart_5247600 := by decide
  rcases family_descends (prefixWord ++ tailWord_5247600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5247618 : List Nat := [3, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4]
def baseStart_5247618 : Nat := 118140960795 + 5247618 * 2 ^ 59
def prefixEnd_5247618 : Nat := 4983230072969 + 3 ^ 40 * 5247618 * 2
def baseEnd_5247618 : Nat := 2694550325185554904141651

theorem tailTrace_5247618 : CollatzResearch.WordTrace tailWord_5247618 prefixEnd_5247618 2694550325185554904141651 := by
  unfold tailWord_5247618
  simp only [CollatzResearch.WordTrace]
  refine ⟨47849088075695920661911877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127597568201855788431765005 47849088075695920661911877)
  ·
    refine ⟨8971704014192985124108477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47849088075695920661911877 8971704014192985124108477)
    ·
      refine ⟨3364389005322369421540679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8971704014192985124108477 3364389005322369421540679)
      ·
        refine ⟨5046583507983554132311019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3364389005322369421540679 5046583507983554132311019)
        ·
          refine ⟨7569875261975331198466529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5046583507983554132311019 7569875261975331198466529)
          ·
            refine ⟨5677406446481498398849897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7569875261975331198466529 5677406446481498398849897)
            ·
              refine ⟨4258054834861123799137423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5677406446481498398849897 4258054834861123799137423)
              ·
                refine ⟨6387082252291685698706135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4258054834861123799137423 6387082252291685698706135)
                ·
                  refine ⟨9580623378437528548059203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6387082252291685698706135 9580623378437528548059203)
                  ·
                    refine ⟨14370935067656292822088805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9580623378437528548059203 14370935067656292822088805)
                    ·
                      refine ⟨2694550325185554904141651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14370935067656292822088805 2694550325185554904141651)
                      ·
                        rfl

theorem cell23_5247618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_5247618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5247618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5247618 prefixEnd_5247618 := by exact prefixLift 5247618
  have htrace : WordTrace (prefixWord ++ tailWord_5247618) baseStart_5247618 baseEnd_5247618 := by
    simpa [prefixWord, tailWord_5247618, baseEnd_5247618] using wordTrace_append hprefix tailTrace_5247618
  have hstable : (prefixWord ++ tailWord_5247618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5247618).length < 2 ^ (prefixWord ++ tailWord_5247618).sum := by decide
  have hdescent : baseEnd_5247618 < baseStart_5247618 := by decide
  rcases family_descends (prefixWord ++ tailWord_5247618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5247634 : List Nat := [3, 2, 3, 1, 2, 3, 1, 2, 2, 1, 3]
def baseStart_5247634 : Nat := 118140960795 + 5247634 * 2 ^ 59
def prefixEnd_5247634 : Nat := 4983230072969 + 3 ^ 40 * 5247634 * 2
def baseEnd_5247634 : Nat := 2694558540876026841541577

theorem tailTrace_5247634 : CollatzResearch.WordTrace tailWord_5247634 prefixEnd_5247634 2694558540876026841541577 := by
  unfold tailWord_5247634
  simp only [CollatzResearch.WordTrace]
  refine ⟨47849233967681429345057489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127597957247150478253486637 47849233967681429345057489)
  ·
    refine ⟨35886925475761072008793117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47849233967681429345057489 35886925475761072008793117)
    ·
      refine ⟨13457597053410402003297419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35886925475761072008793117 13457597053410402003297419)
      ·
        refine ⟨20186395580115603004946129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13457597053410402003297419 20186395580115603004946129)
        ·
          refine ⟨15139796685086702253709597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20186395580115603004946129 15139796685086702253709597)
          ·
            refine ⟨5677423756907513345141099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15139796685086702253709597 5677423756907513345141099)
            ·
              refine ⟨8516135635361270017711649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5677423756907513345141099 8516135635361270017711649)
              ·
                refine ⟨6387101726520952513283737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8516135635361270017711649 6387101726520952513283737)
                ·
                  refine ⟨4790326294890714384962803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6387101726520952513283737 4790326294890714384962803)
                  ·
                    refine ⟨7185489442336071577444205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4790326294890714384962803 7185489442336071577444205)
                    ·
                      refine ⟨2694558540876026841541577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7185489442336071577444205 2694558540876026841541577)
                      ·
                        rfl

theorem cell23_5247634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_5247634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5247634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5247634 prefixEnd_5247634 := by exact prefixLift 5247634
  have htrace : WordTrace (prefixWord ++ tailWord_5247634) baseStart_5247634 baseEnd_5247634 := by
    simpa [prefixWord, tailWord_5247634, baseEnd_5247634] using wordTrace_append hprefix tailTrace_5247634
  have hstable : (prefixWord ++ tailWord_5247634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5247634).length < 2 ^ (prefixWord ++ tailWord_5247634).sum := by decide
  have hdescent : baseEnd_5247634 < baseStart_5247634 := by decide
  rcases family_descends (prefixWord ++ tailWord_5247634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5247680 : List Nat := [2, 1, 1, 2, 4, 2, 3, 3, 5]
def baseStart_5247680 : Nat := 118140960795 + 5247680 * 2 ^ 59
def prefixEnd_5247680 : Nat := 4983230072969 + 3 ^ 40 * 5247680 * 2
def baseEnd_5247680 : Nat := 299398017887348184618485

theorem tailTrace_5247680 : CollatzResearch.WordTrace tailWord_5247680 prefixEnd_5247680 299398017887348184618485 := by
  unfold tailWord_5247680
  simp only [CollatzResearch.WordTrace]
  refine ⟨95699306814279533618202247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127599075752372711490936329 95699306814279533618202247)
  ·
    refine ⟨143548960221419300427303371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95699306814279533618202247 143548960221419300427303371)
    ·
      refine ⟨215323440332128950640955057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143548960221419300427303371 215323440332128950640955057)
      ·
        refine ⟨161492580249096712980716293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215323440332128950640955057 161492580249096712980716293)
        ·
          refine ⟨30279858796705633683884305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 161492580249096712980716293 30279858796705633683884305)
          ·
            refine ⟨22709894097529225262913229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30279858796705633683884305 22709894097529225262913229)
            ·
              refine ⟨8516210286573459473592461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22709894097529225262913229 8516210286573459473592461)
              ·
                refine ⟨3193578857465047302597173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8516210286573459473592461 3193578857465047302597173)
                ·
                  refine ⟨299398017887348184618485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3193578857465047302597173 299398017887348184618485)
                  ·
                    rfl

theorem cell23_5247680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 3, 5].length) (baseStart_5247680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5247680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5247680 prefixEnd_5247680 := by exact prefixLift 5247680
  have htrace : WordTrace (prefixWord ++ tailWord_5247680) baseStart_5247680 baseEnd_5247680 := by
    simpa [prefixWord, tailWord_5247680, baseEnd_5247680] using wordTrace_append hprefix tailTrace_5247680
  have hstable : (prefixWord ++ tailWord_5247680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5247680).length < 2 ^ (prefixWord ++ tailWord_5247680).sum := by decide
  have hdescent : baseEnd_5247680 < baseStart_5247680 := by decide
  rcases family_descends (prefixWord ++ tailWord_5247680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5247703 : List Nat := [1, 1, 3, 2, 1, 5, 1, 1, 1, 2, 5]
def baseStart_5247703 : Nat := 118140960795 + 5247703 * 2 ^ 59
def prefixEnd_5247703 : Nat := 4983230072969 + 3 ^ 40 * 5247703 * 2
def baseEnd_5247703 : Nat := 2694593971041187071578759

theorem tailTrace_5247703 : CollatzResearch.WordTrace tailWord_5247703 prefixEnd_5247703 2694593971041187071578759 := by
  unfold tailWord_5247703
  simp only [CollatzResearch.WordTrace]
  refine ⟨191399452507475742164491763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127599635004983828109661175 191399452507475742164491763)
  ·
    refine ⟨287099178761213613246737645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191399452507475742164491763 287099178761213613246737645)
    ·
      refine ⟨107662192035455104967526617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 287099178761213613246737645 107662192035455104967526617)
      ·
        refine ⟨80746644026591328725644963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107662192035455104967526617 80746644026591328725644963)
        ·
          refine ⟨121119966039886993088467445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80746644026591328725644963 121119966039886993088467445)
          ·
            refine ⟨11354996816239405602043823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 121119966039886993088467445 11354996816239405602043823)
            ·
              refine ⟨17032495224359108403065735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11354996816239405602043823 17032495224359108403065735)
              ·
                refine ⟨25548742836538662604598603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17032495224359108403065735 25548742836538662604598603)
                ·
                  refine ⟨38323114254807993906897905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25548742836538662604598603 38323114254807993906897905)
                  ·
                    refine ⟨28742335691105995430173429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38323114254807993906897905 28742335691105995430173429)
                    ·
                      refine ⟨2694593971041187071578759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28742335691105995430173429 2694593971041187071578759)
                      ·
                        rfl

theorem cell23_5247703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 2, 5].length) (baseStart_5247703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5247703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5247703 prefixEnd_5247703 := by exact prefixLift 5247703
  have htrace : WordTrace (prefixWord ++ tailWord_5247703) baseStart_5247703 baseEnd_5247703 := by
    simpa [prefixWord, tailWord_5247703, baseEnd_5247703] using wordTrace_append hprefix tailTrace_5247703
  have hstable : (prefixWord ++ tailWord_5247703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5247703).length < 2 ^ (prefixWord ++ tailWord_5247703).sum := by decide
  have hdescent : baseEnd_5247703 < baseStart_5247703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5247703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5247708 : List Nat := [2, 2, 5, 1, 1, 3, 2, 1, 2, 2, 2]
def baseStart_5247708 : Nat := 118140960795 + 5247708 * 2 ^ 59
def prefixEnd_5247708 : Nat := 4983230072969 + 3 ^ 40 * 5247708 * 2
def baseEnd_5247708 : Nat := 2694596538444459552016237

theorem tailTrace_5247708 : CollatzResearch.WordTrace tailWord_5247708 prefixEnd_5247708 2694596538444459552016237 := by
  unfold tailWord_5247708
  simp only [CollatzResearch.WordTrace]
  refine ⟨95699817436228814009211889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127599756581638418678949185 95699817436228814009211889)
  ·
    refine ⟨71774863077171610506908917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95699817436228814009211889 71774863077171610506908917)
    ·
      refine ⟨6728893413484838485022711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 71774863077171610506908917 6728893413484838485022711)
      ·
        refine ⟨10093340120227257727534067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6728893413484838485022711 10093340120227257727534067)
        ·
          refine ⟨15140010180340886591301101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10093340120227257727534067 15140010180340886591301101)
          ·
            refine ⟨5677503817627832471737913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15140010180340886591301101 5677503817627832471737913)
            ·
              refine ⟨4258127863220874353803435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5677503817627832471737913 4258127863220874353803435)
              ·
                refine ⟨6387191794831311530705153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4258127863220874353803435 6387191794831311530705153)
                ·
                  refine ⟨4790393846123483648028865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6387191794831311530705153 4790393846123483648028865)
                  ·
                    refine ⟨3592795384592612736021649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4790393846123483648028865 3592795384592612736021649)
                    ·
                      refine ⟨2694596538444459552016237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3592795384592612736021649 2694596538444459552016237)
                      ·
                        rfl

theorem cell23_5247708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_5247708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5247708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5247708 prefixEnd_5247708 := by exact prefixLift 5247708
  have htrace : WordTrace (prefixWord ++ tailWord_5247708) baseStart_5247708 baseEnd_5247708 := by
    simpa [prefixWord, tailWord_5247708, baseEnd_5247708] using wordTrace_append hprefix tailTrace_5247708
  have hstable : (prefixWord ++ tailWord_5247708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5247708).length < 2 ^ (prefixWord ++ tailWord_5247708).sum := by decide
  have hdescent : baseEnd_5247708 < baseStart_5247708 := by decide
  rcases family_descends (prefixWord ++ tailWord_5247708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5247723 : List Nat := [1, 1, 1, 1, 2, 4, 1, 3, 5, 4]
def baseStart_5247723 : Nat := 118140960795 + 5247723 * 2 ^ 59
def prefixEnd_5247723 : Nat := 4983230072969 + 3 ^ 40 * 5247723 * 2
def baseEnd_5247723 : Nat := 898201413551425664442889

theorem tailTrace_5247723 : CollatzResearch.WordTrace tailWord_5247723 prefixEnd_5247723 898201413551425664442889 := by
  unfold tailWord_5247723
  simp only [CollatzResearch.WordTrace]
  refine ⟨191400181967403285580219823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127600121311602190386813215 191400181967403285580219823)
  ·
    refine ⟨287100272951104928370329735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191400181967403285580219823 287100272951104928370329735)
    ·
      refine ⟨430650409426657392555494603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287100272951104928370329735 430650409426657392555494603)
      ·
        refine ⟨645975614139986088833241905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 430650409426657392555494603 645975614139986088833241905)
        ·
          refine ⟨484481710604989566624931429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 645975614139986088833241905 484481710604989566624931429)
          ·
            refine ⟨90840320738435543742174643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 484481710604989566624931429 90840320738435543742174643)
            ·
              refine ⟨136260481107653315613261965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90840320738435543742174643 136260481107653315613261965)
              ·
                refine ⟨51097680415369993354973237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 136260481107653315613261965 51097680415369993354973237)
                ·
                  refine ⟨4790407538940936877028741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51097680415369993354973237 4790407538940936877028741)
                  ·
                    refine ⟨898201413551425664442889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4790407538940936877028741 898201413551425664442889)
                    ·
                      rfl

theorem cell23_5247723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 5, 4].length) (baseStart_5247723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5247723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5247723 prefixEnd_5247723 := by exact prefixLift 5247723
  have htrace : WordTrace (prefixWord ++ tailWord_5247723) baseStart_5247723 baseEnd_5247723 := by
    simpa [prefixWord, tailWord_5247723, baseEnd_5247723] using wordTrace_append hprefix tailTrace_5247723
  have hstable : (prefixWord ++ tailWord_5247723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5247723).length < 2 ^ (prefixWord ++ tailWord_5247723).sum := by decide
  have hdescent : baseEnd_5247723 < baseStart_5247723 := by decide
  rcases family_descends (prefixWord ++ tailWord_5247723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5247730 : List Nat := [3, 2, 1, 3, 1, 2, 1, 3, 2, 1, 4]
def baseStart_5247730 : Nat := 118140960795 + 5247730 * 2 ^ 59
def prefixEnd_5247730 : Nat := 4983230072969 + 3 ^ 40 * 5247730 * 2
def baseEnd_5247730 : Nat := 2694607835018858465941135

theorem tailTrace_5247730 : CollatzResearch.WordTrace tailWord_5247730 prefixEnd_5247730 2694607835018858465941135 := by
  unfold tailWord_5247730
  simp only [CollatzResearch.WordTrace]
  refine ⟨47850109319594481443931161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127600291518918617183816429 47850109319594481443931161)
  ·
    refine ⟨35887581989695861082948371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47850109319594481443931161 35887581989695861082948371)
    ·
      refine ⟨53831372984543791624422557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35887581989695861082948371 53831372984543791624422557)
      ·
        refine ⟨20186764869203921859158459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53831372984543791624422557 20186764869203921859158459)
        ·
          refine ⟨30280147303805882788737689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20186764869203921859158459 30280147303805882788737689)
          ·
            refine ⟨22710110477854412091553267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30280147303805882788737689 22710110477854412091553267)
            ·
              refine ⟨34065165716781618137329901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22710110477854412091553267 34065165716781618137329901)
              ·
                refine ⟨12774437143793106801498713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34065165716781618137329901 12774437143793106801498713)
                ·
                  refine ⟨9580827857844830101124035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12774437143793106801498713 9580827857844830101124035)
                  ·
                    refine ⟨14371241786767245151686053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9580827857844830101124035 14371241786767245151686053)
                    ·
                      refine ⟨2694607835018858465941135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14371241786767245151686053 2694607835018858465941135)
                      ·
                        rfl

theorem cell23_5247730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_5247730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5247730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5247730 prefixEnd_5247730 := by exact prefixLift 5247730
  have htrace : WordTrace (prefixWord ++ tailWord_5247730) baseStart_5247730 baseEnd_5247730 := by
    simpa [prefixWord, tailWord_5247730, baseEnd_5247730] using wordTrace_append hprefix tailTrace_5247730
  have hstable : (prefixWord ++ tailWord_5247730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5247730).length < 2 ^ (prefixWord ++ tailWord_5247730).sum := by decide
  have hdescent : baseEnd_5247730 < baseStart_5247730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5247730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5247753 : List Nat := [1, 2, 1, 1, 3, 2, 3, 4, 6]
def baseStart_5247753 : Nat := 118140960795 + 5247753 * 2 ^ 59
def prefixEnd_5247753 : Nat := 4983230072969 + 3 ^ 40 * 5247753 * 2
def baseEnd_5247753 : Nat := 299402182785990208439281

theorem tailTrace_5247753 : CollatzResearch.WordTrace tailWord_5247753 prefixEnd_5247753 299402182785990208439281 := by
  unfold tailWord_5247753
  simp only [CollatzResearch.WordTrace]
  refine ⟨191401276157294600703811913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127600850771529733802541275 191401276157294600703811913)
  ·
    refine ⟨143550957117970950527858935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191401276157294600703811913 143550957117970950527858935)
    ·
      refine ⟨215326435676956425791788403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143550957117970950527858935 215326435676956425791788403)
      ·
        refine ⟨322989653515434638687682605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215326435676956425791788403 322989653515434638687682605)
        ·
          refine ⟨121121120068287989507880977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 322989653515434638687682605 121121120068287989507880977)
          ·
            refine ⟨90840840051215992130910733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121121120068287989507880977 90840840051215992130910733)
            ·
              refine ⟨34065315019205997049091525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90840840051215992130910733 34065315019205997049091525)
              ·
                refine ⟨6387246566101124446704661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34065315019205997049091525 6387246566101124446704661)
                ·
                  refine ⟨299402182785990208439281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6387246566101124446704661 299402182785990208439281)
                  ·
                    rfl

theorem cell23_5247753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 4, 6].length) (baseStart_5247753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5247753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5247753 prefixEnd_5247753 := by exact prefixLift 5247753
  have htrace : WordTrace (prefixWord ++ tailWord_5247753) baseStart_5247753 baseEnd_5247753 := by
    simpa [prefixWord, tailWord_5247753, baseEnd_5247753] using wordTrace_append hprefix tailTrace_5247753
  have hstable : (prefixWord ++ tailWord_5247753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5247753).length < 2 ^ (prefixWord ++ tailWord_5247753).sum := by decide
  have hdescent : baseEnd_5247753 < baseStart_5247753 := by decide
  rcases family_descends (prefixWord ++ tailWord_5247753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5247800 : List Nat := [2, 1, 2, 1, 3, 2, 3, 3, 1, 5]
def baseStart_5247800 : Nat := 118140960795 + 5247800 * 2 ^ 59
def prefixEnd_5247800 : Nat := 4983230072969 + 3 ^ 40 * 5247800 * 2
def baseEnd_5247800 : Nat := 898214592888224397355271

theorem tailTrace_5247800 : CollatzResearch.WordTrace tailWord_5247800 prefixEnd_5247800 898214592888224397355271 := by
  unfold tailWord_5247800
  simp only [CollatzResearch.WordTrace]
  refine ⟨95701495194062163865386427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127601993592082885153848569 95701495194062163865386427)
  ·
    refine ⟨143552242791093245798079641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95701495194062163865386427 143552242791093245798079641)
    ·
      refine ⟨107664182093319934348559731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143552242791093245798079641 107664182093319934348559731)
      ·
        refine ⟨161496273139979901522839597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107664182093319934348559731 161496273139979901522839597)
        ·
          refine ⟨60561102427492463071064849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161496273139979901522839597 60561102427492463071064849)
          ·
            refine ⟨45420826820619347303298637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60561102427492463071064849 45420826820619347303298637)
            ·
              refine ⟨17032810057732255238736989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45420826820619347303298637 17032810057732255238736989)
              ·
                refine ⟨6387303771649595714526371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17032810057732255238736989 6387303771649595714526371)
                ·
                  refine ⟨9580955657474393571789557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6387303771649595714526371 9580955657474393571789557)
                  ·
                    refine ⟨898214592888224397355271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9580955657474393571789557 898214592888224397355271)
                    ·
                      rfl

theorem cell23_5247800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 3, 1, 5].length) (baseStart_5247800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5247800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5247800 prefixEnd_5247800 := by exact prefixLift 5247800
  have htrace : WordTrace (prefixWord ++ tailWord_5247800) baseStart_5247800 baseEnd_5247800 := by
    simpa [prefixWord, tailWord_5247800, baseEnd_5247800] using wordTrace_append hprefix tailTrace_5247800
  have hstable : (prefixWord ++ tailWord_5247800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5247800).length < 2 ^ (prefixWord ++ tailWord_5247800).sum := by decide
  have hdescent : baseEnd_5247800 < baseStart_5247800 := by decide
  rcases family_descends (prefixWord ++ tailWord_5247800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5247857 : List Nat := [1, 2, 2, 2, 1, 4, 2, 3, 1, 2, 3]
def baseStart_5247857 : Nat := 118140960795 + 5247857 * 2 ^ 59
def prefixEnd_5247857 : Nat := 4983230072969 + 3 ^ 40 * 5247857 * 2
def baseEnd_5247857 : Nat := 2694673047061979469053051

theorem tailTrace_5247857 : CollatzResearch.WordTrace tailWord_5247857 prefixEnd_5247857 2694673047061979469053051 := by
  unfold tailWord_5247857
  simp only [CollatzResearch.WordTrace]
  refine ⟨191405069348917826465597825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127603379565945217643731883 191405069348917826465597825)
  ·
    refine ⟨143553802011688369849198369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191405069348917826465597825 143553802011688369849198369)
    ·
      refine ⟨107665351508766277386898777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143553802011688369849198369 107665351508766277386898777)
      ·
        refine ⟨80749013631574708040174083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107665351508766277386898777 80749013631574708040174083)
        ·
          refine ⟨121123520447362062060261125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80749013631574708040174083 121123520447362062060261125)
          ·
            refine ⟨22710660083880386636298961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 121123520447362062060261125 22710660083880386636298961)
            ·
              refine ⟨17032995062910289977224221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22710660083880386636298961 17032995062910289977224221)
              ·
                refine ⟨6387373148591358741459083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17032995062910289977224221 6387373148591358741459083)
                ·
                  refine ⟨9581059722887038112188625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6387373148591358741459083 9581059722887038112188625)
                  ·
                    refine ⟨7185794792165278584141469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9581059722887038112188625 7185794792165278584141469)
                    ·
                      refine ⟨2694673047061979469053051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7185794792165278584141469 2694673047061979469053051)
                      ·
                        rfl

theorem cell23_5247857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 3, 1, 2, 3].length) (baseStart_5247857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5247857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5247857 prefixEnd_5247857 := by exact prefixLift 5247857
  have htrace : WordTrace (prefixWord ++ tailWord_5247857) baseStart_5247857 baseEnd_5247857 := by
    simpa [prefixWord, tailWord_5247857, baseEnd_5247857] using wordTrace_append hprefix tailTrace_5247857
  have hstable : (prefixWord ++ tailWord_5247857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5247857).length < 2 ^ (prefixWord ++ tailWord_5247857).sum := by decide
  have hdescent : baseEnd_5247857 < baseStart_5247857 := by decide
  rcases family_descends (prefixWord ++ tailWord_5247857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5247894 : List Nat := [5, 3, 1, 1, 1, 1, 2, 9]
def baseStart_5247894 : Nat := 118140960795 + 5247894 * 2 ^ 59
def prefixEnd_5247894 : Nat := 4983230072969 + 3 ^ 40 * 5247894 * 2
def baseEnd_5247894 : Nat := 99803409105414660158903

theorem tailTrace_5247894 : CollatzResearch.WordTrace tailWord_5247894 prefixEnd_5247894 99803409105414660158903 := by
  unfold tailWord_5247894
  simp only [CollatzResearch.WordTrace]
  refine ⟨11962901178111486361543421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 127604279233189187856463157 11962901178111486361543421)
  ·
    refine ⟨4486087941791807385578783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11962901178111486361543421 4486087941791807385578783)
    ·
      refine ⟨6729131912687711078368175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4486087941791807385578783 6729131912687711078368175)
      ·
        refine ⟨10093697869031566617552263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6729131912687711078368175 10093697869031566617552263)
        ·
          refine ⟨15140546803547349926328395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10093697869031566617552263 15140546803547349926328395)
          ·
            refine ⟨22710820205321024889492593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15140546803547349926328395 22710820205321024889492593)
            ·
              refine ⟨17033115153990768667119445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22710820205321024889492593 17033115153990768667119445)
              ·
                refine ⟨99803409105414660158903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17033115153990768667119445 99803409105414660158903)
                ·
                  rfl

theorem cell23_5247894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 9].length) (baseStart_5247894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5247894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5247894 prefixEnd_5247894 := by exact prefixLift 5247894
  have htrace : WordTrace (prefixWord ++ tailWord_5247894) baseStart_5247894 baseEnd_5247894 := by
    simpa [prefixWord, tailWord_5247894, baseEnd_5247894] using wordTrace_append hprefix tailTrace_5247894
  have hstable : (prefixWord ++ tailWord_5247894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5247894).length < 2 ^ (prefixWord ++ tailWord_5247894).sum := by decide
  have hdescent : baseEnd_5247894 < baseStart_5247894 := by decide
  rcases family_descends (prefixWord ++ tailWord_5247894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5247921 : List Nat := [1, 2, 2, 4, 3, 1, 2, 2, 2, 1, 3]
def baseStart_5247921 : Nat := 118140960795 + 5247921 * 2 ^ 59
def prefixEnd_5247921 : Nat := 4983230072969 + 3 ^ 40 * 5247921 * 2
def baseEnd_5247921 : Nat := 2694705909823867218652757

theorem tailTrace_5247921 : CollatzResearch.WordTrace tailWord_5247921 prefixEnd_5247921 2694705909823867218652757 := by
  unfold tailWord_5247921
  simp only [CollatzResearch.WordTrace]
  refine ⟨191407403620685965395927617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127604935747123976930618411 191407403620685965395927617)
  ·
    refine ⟨143555552715514474046945713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191407403620685965395927617 143555552715514474046945713)
    ·
      refine ⟨107666664536635855535209285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143555552715514474046945713 107666664536635855535209285)
      ·
        refine ⟨20187499600619222912851741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107666664536635855535209285 20187499600619222912851741)
        ·
          refine ⟨7570312350232208592319403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20187499600619222912851741 7570312350232208592319403)
          ·
            refine ⟨11355468525348312888479105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7570312350232208592319403 11355468525348312888479105)
            ·
              refine ⟨8516601394011234666359329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11355468525348312888479105 8516601394011234666359329)
              ·
                refine ⟨6387451045508425999769497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8516601394011234666359329 6387451045508425999769497)
                ·
                  refine ⟨4790588284131319499827123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6387451045508425999769497 4790588284131319499827123)
                  ·
                    refine ⟨7185882426196979249740685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4790588284131319499827123 7185882426196979249740685)
                    ·
                      refine ⟨2694705909823867218652757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7185882426196979249740685 2694705909823867218652757)
                      ·
                        rfl

theorem cell23_5247921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_5247921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5247921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5247921 prefixEnd_5247921 := by exact prefixLift 5247921
  have htrace : WordTrace (prefixWord ++ tailWord_5247921) baseStart_5247921 baseEnd_5247921 := by
    simpa [prefixWord, tailWord_5247921, baseEnd_5247921] using wordTrace_append hprefix tailTrace_5247921
  have hstable : (prefixWord ++ tailWord_5247921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5247921).length < 2 ^ (prefixWord ++ tailWord_5247921).sum := by decide
  have hdescent : baseEnd_5247921 < baseStart_5247921 := by decide
  rcases family_descends (prefixWord ++ tailWord_5247921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5247930 : List Nat := [3, 1, 1, 1, 2, 1, 3, 1, 1, 6, 3]
def baseStart_5247930 : Nat := 118140960795 + 5247930 * 2 ^ 59
def prefixEnd_5247930 : Nat := 4983230072969 + 3 ^ 40 * 5247930 * 2
def baseEnd_5247930 : Nat := 2694710531149757683440215

theorem tailTrace_5247930 : CollatzResearch.WordTrace tailWord_5247930 prefixEnd_5247930 2694710531149757683440215 := by
  unfold tailWord_5247930
  simp only [CollatzResearch.WordTrace]
  refine ⟨47851932969413339983251311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127605154585102239955336829 47851932969413339983251311)
  ·
    refine ⟨71777899454120009974876967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47851932969413339983251311 71777899454120009974876967)
    ·
      refine ⟨107666849181180014962315451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71777899454120009974876967 107666849181180014962315451)
      ·
        refine ⟨161500273771770022443473177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107666849181180014962315451 161500273771770022443473177)
        ·
          refine ⟨121125205328827516832604883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161500273771770022443473177 121125205328827516832604883)
          ·
            refine ⟨181687807993241275248907325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121125205328827516832604883 181687807993241275248907325)
            ·
              refine ⟨68132927997465478218340247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 181687807993241275248907325 68132927997465478218340247)
              ·
                refine ⟨102199391996198217327510371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68132927997465478218340247 102199391996198217327510371)
                ·
                  refine ⟨153299087994297325991265557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102199391996198217327510371 153299087994297325991265557)
                  ·
                    refine ⟨7185894749732687155840573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 153299087994297325991265557 7185894749732687155840573)
                    ·
                      refine ⟨2694710531149757683440215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7185894749732687155840573 2694710531149757683440215)
                      ·
                        rfl

theorem cell23_5247930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 1, 6, 3].length) (baseStart_5247930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5247930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5247930 prefixEnd_5247930 := by exact prefixLift 5247930
  have htrace : WordTrace (prefixWord ++ tailWord_5247930) baseStart_5247930 baseEnd_5247930 := by
    simpa [prefixWord, tailWord_5247930, baseEnd_5247930] using wordTrace_append hprefix tailTrace_5247930
  have hstable : (prefixWord ++ tailWord_5247930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5247930).length < 2 ^ (prefixWord ++ tailWord_5247930).sum := by decide
  have hdescent : baseEnd_5247930 < baseStart_5247930 := by decide
  rcases family_descends (prefixWord ++ tailWord_5247930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5247950 : List Nat := [4, 1, 1, 1, 2, 3, 1, 1, 9]
def baseStart_5247950 : Nat := 118140960795 + 5247950 * 2 ^ 59
def prefixEnd_5247950 : Nat := 4983230072969 + 3 ^ 40 * 5247950 * 2
def baseEnd_5247950 : Nat := 299413422306983067243347

theorem tailTrace_5247950 : CollatzResearch.WordTrace tailWord_5247950 prefixEnd_5247950 299413422306983067243347 := by
  unfold tailWord_5247950
  simp only [CollatzResearch.WordTrace]
  refine ⟨23926057667197612918591663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127605640891720602232488869 23926057667197612918591663)
  ·
    refine ⟨35889086500796419377887495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23926057667197612918591663 35889086500796419377887495)
    ·
      refine ⟨53833629751194629066831243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35889086500796419377887495 53833629751194629066831243)
      ·
        refine ⟨80750444626791943600246865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53833629751194629066831243 80750444626791943600246865)
        ·
          refine ⟨60562833470093957700185149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80750444626791943600246865 60562833470093957700185149)
          ·
            refine ⟨22711062551285234137569431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60562833470093957700185149 22711062551285234137569431)
            ·
              refine ⟨34066593826927851206354147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22711062551285234137569431 34066593826927851206354147)
              ·
                refine ⟨51099890740391776809531221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34066593826927851206354147 51099890740391776809531221)
                ·
                  refine ⟨299413422306983067243347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 51099890740391776809531221 299413422306983067243347)
                  ·
                    rfl

theorem cell23_5247950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 9].length) (baseStart_5247950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5247950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5247950 prefixEnd_5247950 := by exact prefixLift 5247950
  have htrace : WordTrace (prefixWord ++ tailWord_5247950) baseStart_5247950 baseEnd_5247950 := by
    simpa [prefixWord, tailWord_5247950, baseEnd_5247950] using wordTrace_append hprefix tailTrace_5247950
  have hstable : (prefixWord ++ tailWord_5247950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5247950).length < 2 ^ (prefixWord ++ tailWord_5247950).sum := by decide
  have hdescent : baseEnd_5247950 < baseStart_5247950 := by decide
  rcases family_descends (prefixWord ++ tailWord_5247950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5247978 : List Nat := [3, 1, 3, 1, 2, 4, 1, 2, 2, 2, 2]
def baseStart_5247978 : Nat := 118140960795 + 5247978 * 2 ^ 59
def prefixEnd_5247978 : Nat := 4983230072969 + 3 ^ 40 * 5247978 * 2
def baseEnd_5247978 : Nat := 2694735178221173495639995

theorem tailTrace_5247978 : CollatzResearch.WordTrace tailWord_5247978 prefixEnd_5247978 2694735178221173495639995 := by
  unfold tailWord_5247978
  simp only [CollatzResearch.WordTrace]
  refine ⟨47852370645369866032688147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127606321720986309420501725 47852370645369866032688147)
  ·
    refine ⟨71778555968054799049032221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47852370645369866032688147 71778555968054799049032221)
    ·
      refine ⟨26916958488020549643387083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71778555968054799049032221 26916958488020549643387083)
      ·
        refine ⟨40375437732030824465080625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26916958488020549643387083 40375437732030824465080625)
        ·
          refine ⟨30281578299023118348810469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40375437732030824465080625 30281578299023118348810469)
          ·
            refine ⟨5677795931066834690401963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30281578299023118348810469 5677795931066834690401963)
            ·
              refine ⟨8516693896600252035602945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5677795931066834690401963 8516693896600252035602945)
              ·
                refine ⟨6387520422450189026702209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8516693896600252035602945 6387520422450189026702209)
                ·
                  refine ⟨4790640316837641770026657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6387520422450189026702209 4790640316837641770026657)
                  ·
                    refine ⟨3592980237628231327519993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4790640316837641770026657 3592980237628231327519993)
                    ·
                      refine ⟨2694735178221173495639995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3592980237628231327519993 2694735178221173495639995)
                      ·
                        rfl

theorem cell23_5247978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 2, 2, 2, 2].length) (baseStart_5247978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5247978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5247978 prefixEnd_5247978 := by exact prefixLift 5247978
  have htrace : WordTrace (prefixWord ++ tailWord_5247978) baseStart_5247978 baseEnd_5247978 := by
    simpa [prefixWord, tailWord_5247978, baseEnd_5247978] using wordTrace_append hprefix tailTrace_5247978
  have hstable : (prefixWord ++ tailWord_5247978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5247978).length < 2 ^ (prefixWord ++ tailWord_5247978).sum := by decide
  have hdescent : baseEnd_5247978 < baseStart_5247978 := by decide
  rcases family_descends (prefixWord ++ tailWord_5247978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5248017 : List Nat := [1, 2, 2, 1, 1, 2, 1, 4, 1, 6, 2]
def baseStart_5248017 : Nat := 118140960795 + 5248017 * 2 ^ 59
def prefixEnd_5248017 : Nat := 4983230072969 + 3 ^ 40 * 5248017 * 2
def baseEnd_5248017 : Nat := 2694755203966698843052315

theorem tailTrace_5248017 : CollatzResearch.WordTrace tailWord_5248017 prefixEnd_5248017 2694755203966698843052315 := by
  unfold tailWord_5248017
  simp only [CollatzResearch.WordTrace]
  refine ⟨191410905028338173791422305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127607270018892115860948203 191410905028338173791422305)
  ·
    refine ⟨143558178771253630343566729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191410905028338173791422305 143558178771253630343566729)
    ·
      refine ⟨107668634078440222757675047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143558178771253630343566729 107668634078440222757675047)
      ·
        refine ⟨161502951117660334136512571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107668634078440222757675047 161502951117660334136512571)
        ·
          refine ⟨242254426676490501204768857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161502951117660334136512571 242254426676490501204768857)
          ·
            refine ⟨181690820007367875903576643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 242254426676490501204768857 181690820007367875903576643)
            ·
              refine ⟨272536230011051813855364965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181690820007367875903576643 272536230011051813855364965)
              ·
                refine ⟨51100543127072215097880931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 272536230011051813855364965 51100543127072215097880931)
                ·
                  refine ⟨76650814690608322646821397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51100543127072215097880931 76650814690608322646821397)
                  ·
                    refine ⟨3593006938622265124069753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 76650814690608322646821397 3593006938622265124069753)
                    ·
                      refine ⟨2694755203966698843052315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3593006938622265124069753 2694755203966698843052315)
                      ·
                        rfl

theorem cell23_5248017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 6, 2].length) (baseStart_5248017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5248017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5248017 prefixEnd_5248017 := by exact prefixLift 5248017
  have htrace : WordTrace (prefixWord ++ tailWord_5248017) baseStart_5248017 baseEnd_5248017 := by
    simpa [prefixWord, tailWord_5248017, baseEnd_5248017] using wordTrace_append hprefix tailTrace_5248017
  have hstable : (prefixWord ++ tailWord_5248017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5248017).length < 2 ^ (prefixWord ++ tailWord_5248017).sum := by decide
  have hdescent : baseEnd_5248017 < baseStart_5248017 := by decide
  rcases family_descends (prefixWord ++ tailWord_5248017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5248034 : List Nat := [3, 3, 1, 1, 1, 4, 1, 2, 2, 1, 4]
def baseStart_5248034 : Nat := 118140960795 + 5248034 * 2 ^ 59
def prefixEnd_5248034 : Nat := 4983230072969 + 3 ^ 40 * 5248034 * 2
def baseEnd_5248034 : Nat := 2694763933137825276539737

theorem tailTrace_5248034 : CollatzResearch.WordTrace tailWord_5248034 prefixEnd_5248034 2694763933137825276539737 := by
  unfold tailWord_5248034
  simp only [CollatzResearch.WordTrace]
  refine ⟨47852881267319146423697789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127607683379517723796527437 47852881267319146423697789)
  ·
    refine ⟨17944830475244679908886671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47852881267319146423697789 17944830475244679908886671)
    ·
      refine ⟨26917245712867019863330007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17944830475244679908886671 26917245712867019863330007)
      ·
        refine ⟨40375868569300529794995011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26917245712867019863330007 40375868569300529794995011)
        ·
          refine ⟨60563802853950794692492517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40375868569300529794995011 60563802853950794692492517)
          ·
            refine ⟨11355713035115774004842347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60563802853950794692492517 11355713035115774004842347)
            ·
              refine ⟨17033569552673661007263521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11355713035115774004842347 17033569552673661007263521)
              ·
                refine ⟨12775177164505245755447641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17033569552673661007263521 12775177164505245755447641)
                ·
                  refine ⟨9581382873378934316585731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12775177164505245755447641 9581382873378934316585731)
                  ·
                    refine ⟨14372074310068401474878597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9581382873378934316585731 14372074310068401474878597)
                    ·
                      refine ⟨2694763933137825276539737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14372074310068401474878597 2694763933137825276539737)
                      ·
                        rfl

theorem cell23_5248034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_5248034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5248034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5248034 prefixEnd_5248034 := by exact prefixLift 5248034
  have htrace : WordTrace (prefixWord ++ tailWord_5248034) baseStart_5248034 baseEnd_5248034 := by
    simpa [prefixWord, tailWord_5248034, baseEnd_5248034] using wordTrace_append hprefix tailTrace_5248034
  have hstable : (prefixWord ++ tailWord_5248034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5248034).length < 2 ^ (prefixWord ++ tailWord_5248034).sum := by decide
  have hdescent : baseEnd_5248034 < baseStart_5248034 := by decide
  rcases family_descends (prefixWord ++ tailWord_5248034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5248080 : List Nat := [2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 7]
def baseStart_5248080 : Nat := 118140960795 + 5248080 * 2 ^ 59
def prefixEnd_5248080 : Nat := 4983230072969 + 3 ^ 40 * 5248080 * 2
def baseEnd_5248080 : Nat := 2694787553247932096564525

theorem tailTrace_5248080 : CollatzResearch.WordTrace tailWord_5248080 prefixEnd_5248080 2694787553247932096564525 := by
  unfold tailWord_5248080
  simp only [CollatzResearch.WordTrace]
  refine ⟨95706601413554967775482847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127608801884739957033977129 95706601413554967775482847)
  ·
    refine ⟨143559902120332451663224271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95706601413554967775482847 143559902120332451663224271)
    ·
      refine ⟨215339853180498677494836407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143559902120332451663224271 215339853180498677494836407)
      ·
        refine ⟨323009779770748016242254611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215339853180498677494836407 323009779770748016242254611)
        ·
          refine ⟨484514669656122024363381917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323009779770748016242254611 484514669656122024363381917)
          ·
            refine ⟨181693001121045759136268219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 484514669656122024363381917 181693001121045759136268219)
            ·
              refine ⟨272539501681568638704402329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181693001121045759136268219 272539501681568638704402329)
              ·
                refine ⟨204404626261176479028301747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 272539501681568638704402329 204404626261176479028301747)
                ·
                  refine ⟨306606939391764718542452621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 204404626261176479028301747 306606939391764718542452621)
                  ·
                    refine ⟨114977602271911769453419733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 306606939391764718542452621 114977602271911769453419733)
                    ·
                      refine ⟨2694787553247932096564525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 114977602271911769453419733 2694787553247932096564525)
                      ·
                        rfl

theorem cell23_5248080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 7].length) (baseStart_5248080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5248080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5248080 prefixEnd_5248080 := by exact prefixLift 5248080
  have htrace : WordTrace (prefixWord ++ tailWord_5248080) baseStart_5248080 baseEnd_5248080 := by
    simpa [prefixWord, tailWord_5248080, baseEnd_5248080] using wordTrace_append hprefix tailTrace_5248080
  have hstable : (prefixWord ++ tailWord_5248080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5248080).length < 2 ^ (prefixWord ++ tailWord_5248080).sum := by decide
  have hdescent : baseEnd_5248080 < baseStart_5248080 := by decide
  rcases family_descends (prefixWord ++ tailWord_5248080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5248124 : List Nat := [2, 2, 2, 1, 1, 3, 2, 4, 1, 1, 4]
def baseStart_5248124 : Nat := 118140960795 + 5248124 * 2 ^ 59
def prefixEnd_5248124 : Nat := 4983230072969 + 3 ^ 40 * 5248124 * 2
def baseEnd_5248124 : Nat := 2694810146396729924414323

theorem tailTrace_5248124 : CollatzResearch.WordTrace tailWord_5248124 prefixEnd_5248124 2694810146396729924414323 := by
  unfold tailWord_5248124
  simp only [CollatzResearch.WordTrace]
  refine ⟨95707403819475265532783713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127609871759300354043711617 95707403819475265532783713)
  ·
    refine ⟨71780552864606449149587785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95707403819475265532783713 71780552864606449149587785)
    ·
      refine ⟨53835414648454836862190839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71780552864606449149587785 53835414648454836862190839)
      ·
        refine ⟨80753121972682255293286259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53835414648454836862190839 80753121972682255293286259)
        ·
          refine ⟨121129682959023382939929389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80753121972682255293286259 121129682959023382939929389)
          ·
            refine ⟨45423631109633768602473521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121129682959023382939929389 45423631109633768602473521)
            ·
              refine ⟨34067723332225326451855141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45423631109633768602473521 34067723332225326451855141)
              ·
                refine ⟨6387698124792248709722839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34067723332225326451855141 6387698124792248709722839)
                ·
                  refine ⟨9581547187188373064584259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6387698124792248709722839 9581547187188373064584259)
                  ·
                    refine ⟨14372320780782559596876389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9581547187188373064584259 14372320780782559596876389)
                    ·
                      refine ⟨2694810146396729924414323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14372320780782559596876389 2694810146396729924414323)
                      ·
                        rfl

theorem cell23_5248124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 4, 1, 1, 4].length) (baseStart_5248124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5248124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5248124 prefixEnd_5248124 := by exact prefixLift 5248124
  have htrace : WordTrace (prefixWord ++ tailWord_5248124) baseStart_5248124 baseEnd_5248124 := by
    simpa [prefixWord, tailWord_5248124, baseEnd_5248124] using wordTrace_append hprefix tailTrace_5248124
  have hstable : (prefixWord ++ tailWord_5248124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5248124).length < 2 ^ (prefixWord ++ tailWord_5248124).sum := by decide
  have hdescent : baseEnd_5248124 < baseStart_5248124 := by decide
  rcases family_descends (prefixWord ++ tailWord_5248124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5248151 : List Nat := [1, 1, 3, 3, 3, 1, 3, 2, 2, 4]
def baseStart_5248151 : Nat := 118140960795 + 5248151 * 2 ^ 59
def prefixEnd_5248151 : Nat := 4983230072969 + 3 ^ 40 * 5248151 * 2
def baseEnd_5248151 : Nat := 898274670124800439592233

theorem tailTrace_5248151 : CollatzResearch.WordTrace tailWord_5248151 prefixEnd_5248151 898274670124800439592233 := by
  unfold tailWord_5248151
  simp only [CollatzResearch.WordTrace]
  refine ⟨191415792409852714676800307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127610528273235143117866871 191415792409852714676800307)
  ·
    refine ⟨287123688614779072015200461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191415792409852714676800307 287123688614779072015200461)
    ·
      refine ⟨107671383230542152005700173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 287123688614779072015200461 107671383230542152005700173)
      ·
        refine ⟨40376768711453307002137565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107671383230542152005700173 40376768711453307002137565)
        ·
          refine ⟨15141288266794990125801587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40376768711453307002137565 15141288266794990125801587)
          ·
            refine ⟨22711932400192485188702381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15141288266794990125801587 22711932400192485188702381)
            ·
              refine ⟨8516974650072181945763393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22711932400192485188702381 8516974650072181945763393)
              ·
                refine ⟨6387730987554136459322545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8516974650072181945763393 6387730987554136459322545)
                ·
                  refine ⟨4790798240665602344491909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6387730987554136459322545 4790798240665602344491909)
                  ·
                    refine ⟨898274670124800439592233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4790798240665602344491909 898274670124800439592233)
                    ·
                      rfl

theorem cell23_5248151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 2, 2, 4].length) (baseStart_5248151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5248151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5248151 prefixEnd_5248151 := by exact prefixLift 5248151
  have htrace : WordTrace (prefixWord ++ tailWord_5248151) baseStart_5248151 baseEnd_5248151 := by
    simpa [prefixWord, tailWord_5248151, baseEnd_5248151] using wordTrace_append hprefix tailTrace_5248151
  have hstable : (prefixWord ++ tailWord_5248151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5248151).length < 2 ^ (prefixWord ++ tailWord_5248151).sum := by decide
  have hdescent : baseEnd_5248151 < baseStart_5248151 := by decide
  rcases family_descends (prefixWord ++ tailWord_5248151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5248192 : List Nat := [2, 1, 1, 2, 6, 2, 1, 3, 1, 2, 2]
def baseStart_5248192 : Nat := 118140960795 + 5248192 * 2 ^ 59
def prefixEnd_5248192 : Nat := 4983230072969 + 3 ^ 40 * 5248192 * 2
def baseEnd_5248192 : Nat := 2694845063081235658364011

theorem tailTrace_5248192 : CollatzResearch.WordTrace tailWord_5248192 prefixEnd_5248192 2694845063081235658364011 := by
  unfold tailWord_5248192
  simp only [CollatzResearch.WordTrace]
  refine ⟨95708643901352089339521415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127611525201802785786028553 95708643901352089339521415)
  ·
    refine ⟨143562965852028134009282123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95708643901352089339521415 143562965852028134009282123)
    ·
      refine ⟨215344448778042201013923185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143562965852028134009282123 215344448778042201013923185)
      ·
        refine ⟨161508336583531650760442389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215344448778042201013923185 161508336583531650760442389)
        ·
          refine ⟨7570703277353046129395737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 161508336583531650760442389 7570703277353046129395737)
          ·
            refine ⟨5678027458014784597046803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7570703277353046129395737 5678027458014784597046803)
            ·
              refine ⟨8517041187022176895570205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5678027458014784597046803 8517041187022176895570205)
              ·
                refine ⟨3193890445133316335838827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8517041187022176895570205 3193890445133316335838827)
                ·
                  refine ⟨4790835667699974503758241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3193890445133316335838827 4790835667699974503758241)
                  ·
                    refine ⟨3593126750774980877818681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4790835667699974503758241 3593126750774980877818681)
                    ·
                      refine ⟨2694845063081235658364011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3593126750774980877818681 2694845063081235658364011)
                      ·
                        rfl

theorem cell23_5248192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 3, 1, 2, 2].length) (baseStart_5248192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5248192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5248192 prefixEnd_5248192 := by exact prefixLift 5248192
  have htrace : WordTrace (prefixWord ++ tailWord_5248192) baseStart_5248192 baseEnd_5248192 := by
    simpa [prefixWord, tailWord_5248192, baseEnd_5248192] using wordTrace_append hprefix tailTrace_5248192
  have hstable : (prefixWord ++ tailWord_5248192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5248192).length < 2 ^ (prefixWord ++ tailWord_5248192).sum := by decide
  have hdescent : baseEnd_5248192 < baseStart_5248192 := by decide
  rcases family_descends (prefixWord ++ tailWord_5248192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5248197 : List Nat := [1, 3, 1, 1, 1, 1, 3, 2, 1, 5, 4]
def baseStart_5248197 : Nat := 118140960795 + 5248197 * 2 ^ 59
def prefixEnd_5248197 : Nat := 4983230072969 + 3 ^ 40 * 5248197 * 2
def baseEnd_5248197 : Nat := 2694847630484508138801487

theorem tailTrace_5248197 : CollatzResearch.WordTrace tailWord_5248197 prefixEnd_5248197 2694847630484508138801487 := by
  unfold tailWord_5248197
  simp only [CollatzResearch.WordTrace]
  refine ⟨191417470167686064532974845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127611646778457376355316563 191417470167686064532974845)
  ·
    refine ⟨71781551312882274199865567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191417470167686064532974845 71781551312882274199865567)
    ·
      refine ⟨107672326969323411299798351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71781551312882274199865567 107672326969323411299798351)
      ·
        refine ⟨161508490453985116949697527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107672326969323411299798351 161508490453985116949697527)
        ·
          refine ⟨242262735680977675424546291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161508490453985116949697527 242262735680977675424546291)
          ·
            refine ⟨363394103521466513136819437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242262735680977675424546291 363394103521466513136819437)
            ·
              refine ⟨136272788820549942426307289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 363394103521466513136819437 136272788820549942426307289)
              ·
                refine ⟨102204591615412456819730467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136272788820549942426307289 102204591615412456819730467)
                ·
                  refine ⟨153306887423118685229595701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102204591615412456819730467 153306887423118685229595701)
                  ·
                    refine ⟨14372520695917376740274597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 153306887423118685229595701 14372520695917376740274597)
                    ·
                      refine ⟨2694847630484508138801487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14372520695917376740274597 2694847630484508138801487)
                      ·
                        rfl

theorem cell23_5248197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 5, 4].length) (baseStart_5248197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5248197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5248197 prefixEnd_5248197 := by exact prefixLift 5248197
  have htrace : WordTrace (prefixWord ++ tailWord_5248197) baseStart_5248197 baseEnd_5248197 := by
    simpa [prefixWord, tailWord_5248197, baseEnd_5248197] using wordTrace_append hprefix tailTrace_5248197
  have hstable : (prefixWord ++ tailWord_5248197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5248197).length < 2 ^ (prefixWord ++ tailWord_5248197).sum := by decide
  have hdescent : baseEnd_5248197 < baseStart_5248197 := by decide
  rcases family_descends (prefixWord ++ tailWord_5248197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5248207 : List Nat := [1, 1, 2, 1, 1, 3, 2, 4, 2, 6]
def baseStart_5248207 : Nat := 118140960795 + 5248207 * 2 ^ 59
def prefixEnd_5248207 : Nat := 4983230072969 + 3 ^ 40 * 5248207 * 2
def baseEnd_5248207 : Nat := 898284255097017699892147

theorem tailTrace_5248207 : CollatzResearch.WordTrace tailWord_5248207 prefixEnd_5248207 898284255097017699892147 := by
  unfold tailWord_5248207
  simp only [CollatzResearch.WordTrace]
  refine ⟨191417834897649836240838875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127611889931766557493892583 191417834897649836240838875)
  ·
    refine ⟨287126752346474754361258313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191417834897649836240838875 287126752346474754361258313)
    ·
      refine ⟨215345064259856065770943735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287126752346474754361258313 215345064259856065770943735)
      ·
        refine ⟨323017596389784098656415603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215345064259856065770943735 323017596389784098656415603)
        ·
          refine ⟨484526394584676147984623405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323017596389784098656415603 484526394584676147984623405)
          ·
            refine ⟨181697397969253555494233777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 484526394584676147984623405 181697397969253555494233777)
            ·
              refine ⟨136273048476940166620675333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 181697397969253555494233777 136273048476940166620675333)
              ·
                refine ⟨25551196589426281241376625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 136273048476940166620675333 25551196589426281241376625)
                ·
                  refine ⟨19163397442069710931032469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25551196589426281241376625 19163397442069710931032469)
                  ·
                    refine ⟨898284255097017699892147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19163397442069710931032469 898284255097017699892147)
                    ·
                      rfl

theorem cell23_5248207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 2, 6].length) (baseStart_5248207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5248207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5248207 prefixEnd_5248207 := by exact prefixLift 5248207
  have htrace : WordTrace (prefixWord ++ tailWord_5248207) baseStart_5248207 baseEnd_5248207 := by
    simpa [prefixWord, tailWord_5248207, baseEnd_5248207] using wordTrace_append hprefix tailTrace_5248207
  have hstable : (prefixWord ++ tailWord_5248207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5248207).length < 2 ^ (prefixWord ++ tailWord_5248207).sum := by decide
  have hdescent : baseEnd_5248207 < baseStart_5248207 := by decide
  rcases family_descends (prefixWord ++ tailWord_5248207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5248217 : List Nat := [1, 2, 1, 2, 3, 1, 1, 1, 3, 3, 5]
def baseStart_5248217 : Nat := 118140960795 + 5248217 * 2 ^ 59
def prefixEnd_5248217 : Nat := 4983230072969 + 3 ^ 40 * 5248217 * 2
def baseEnd_5248217 : Nat := 2694857900097598060551395

theorem tailTrace_5248217 : CollatzResearch.WordTrace tailWord_5248217 prefixEnd_5248217 2694857900097598060551395 := by
  unfold tailWord_5248217
  simp only [CollatzResearch.WordTrace]
  refine ⟨191418199627613607948702905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127612133085075738632468603 191418199627613607948702905)
  ·
    refine ⟨143563649720710205961527179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191418199627613607948702905 143563649720710205961527179)
    ·
      refine ⟨215345474581065308942290769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143563649720710205961527179 215345474581065308942290769)
      ·
        refine ⟨161509105935798981706718077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215345474581065308942290769 161509105935798981706718077)
        ·
          refine ⟨60565914725924618140019279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161509105935798981706718077 60565914725924618140019279)
          ·
            refine ⟨90848872088886927210028919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60565914725924618140019279 90848872088886927210028919)
            ·
              refine ⟨136273308133330390815043379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90848872088886927210028919 136273308133330390815043379)
              ·
                refine ⟨204409962199995586222565069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136273308133330390815043379 204409962199995586222565069)
                ·
                  refine ⟨76653735824998344833461901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 204409962199995586222565069 76653735824998344833461901)
                  ·
                    refine ⟨28745150934374379312548213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 76653735824998344833461901 28745150934374379312548213)
                    ·
                      refine ⟨2694857900097598060551395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28745150934374379312548213 2694857900097598060551395)
                      ·
                        rfl

theorem cell23_5248217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 3, 5].length) (baseStart_5248217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5248217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5248217 prefixEnd_5248217 := by exact prefixLift 5248217
  have htrace : WordTrace (prefixWord ++ tailWord_5248217) baseStart_5248217 baseEnd_5248217 := by
    simpa [prefixWord, tailWord_5248217, baseEnd_5248217] using wordTrace_append hprefix tailTrace_5248217
  have hstable : (prefixWord ++ tailWord_5248217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5248217).length < 2 ^ (prefixWord ++ tailWord_5248217).sum := by decide
  have hdescent : baseEnd_5248217 < baseStart_5248217 := by decide
  rcases family_descends (prefixWord ++ tailWord_5248217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5248225 : List Nat := [1, 2, 3, 1, 3, 4, 2, 1, 2, 1, 3]
def baseStart_5248225 : Nat := 118140960795 + 5248225 * 2 ^ 59
def prefixEnd_5248225 : Nat := 4983230072969 + 3 ^ 40 * 5248225 * 2
def baseEnd_5248225 : Nat := 2694862007942834029251359

theorem tailTrace_5248225 : CollatzResearch.WordTrace tailWord_5248225 prefixEnd_5248225 2694862007942834029251359 := by
  unfold tailWord_5248225
  simp only [CollatzResearch.WordTrace]
  refine ⟨191418491411584625314994129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127612327607723083543329419 191418491411584625314994129)
  ·
    refine ⟨143563868558688468986245597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191418491411584625314994129 143563868558688468986245597)
    ·
      refine ⟨53836450709508175869842099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143563868558688468986245597 53836450709508175869842099)
      ·
        refine ⟨80754676064262263804763149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53836450709508175869842099 80754676064262263804763149)
        ·
          refine ⟨30283003524098348926786181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80754676064262263804763149 30283003524098348926786181)
          ·
            refine ⟨5678063160768440423772409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30283003524098348926786181 5678063160768440423772409)
            ·
              refine ⟨4258547370576330317829307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5678063160768440423772409 4258547370576330317829307)
              ·
                refine ⟨6387821055864495476743961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4258547370576330317829307 6387821055864495476743961)
                ·
                  refine ⟨4790865791898371607557971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6387821055864495476743961 4790865791898371607557971)
                  ·
                    refine ⟨7186298687847557411336957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4790865791898371607557971 7186298687847557411336957)
                    ·
                      refine ⟨2694862007942834029251359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7186298687847557411336957 2694862007942834029251359)
                      ·
                        rfl

theorem cell23_5248225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 2, 1, 2, 1, 3].length) (baseStart_5248225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5248225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5248225 prefixEnd_5248225 := by exact prefixLift 5248225
  have htrace : WordTrace (prefixWord ++ tailWord_5248225) baseStart_5248225 baseEnd_5248225 := by
    simpa [prefixWord, tailWord_5248225, baseEnd_5248225] using wordTrace_append hprefix tailTrace_5248225
  have hstable : (prefixWord ++ tailWord_5248225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5248225).length < 2 ^ (prefixWord ++ tailWord_5248225).sum := by decide
  have hdescent : baseEnd_5248225 < baseStart_5248225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5248225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5248234 : List Nat := [3, 1, 3, 1, 1, 3, 1, 2, 2, 1, 5]
def baseStart_5248234 : Nat := 118140960795 + 5248234 * 2 ^ 59
def prefixEnd_5248234 : Nat := 4983230072969 + 3 ^ 40 * 5248234 * 2
def baseEnd_5248234 : Nat := 2694866629268724494038817

theorem tailTrace_5248234 : CollatzResearch.WordTrace tailWord_5248234 prefixEnd_5248234 2694866629268724494038817 := by
  unfold tailWord_5248234
  simp only [CollatzResearch.WordTrace]
  refine ⟨47854704917138004963017939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127612546445701346568047837 47854704917138004963017939)
  ·
    refine ⟨71782057375707007444526909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47854704917138004963017939 71782057375707007444526909)
    ·
      refine ⟨26918271515890127791697591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71782057375707007444526909 26918271515890127791697591)
      ·
        refine ⟨40377407273835191687546387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26918271515890127791697591 40377407273835191687546387)
        ·
          refine ⟨60566110910752787531319581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40377407273835191687546387 60566110910752787531319581)
          ·
            refine ⟨22712291591532295324244843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60566110910752787531319581 22712291591532295324244843)
            ·
              refine ⟨34068437387298442986367265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22712291591532295324244843 34068437387298442986367265)
              ·
                refine ⟨25551328040473832239775449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34068437387298442986367265 25551328040473832239775449)
                ·
                  refine ⟨19163496030355374179831587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25551328040473832239775449 19163496030355374179831587)
                  ·
                    refine ⟨28745244045533061269747381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19163496030355374179831587 28745244045533061269747381)
                    ·
                      refine ⟨2694866629268724494038817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28745244045533061269747381 2694866629268724494038817)
                      ·
                        rfl

theorem cell23_5248234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_5248234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5248234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5248234 prefixEnd_5248234 := by exact prefixLift 5248234
  have htrace : WordTrace (prefixWord ++ tailWord_5248234) baseStart_5248234 baseEnd_5248234 := by
    simpa [prefixWord, tailWord_5248234, baseEnd_5248234] using wordTrace_append hprefix tailTrace_5248234
  have hstable : (prefixWord ++ tailWord_5248234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5248234).length < 2 ^ (prefixWord ++ tailWord_5248234).sum := by decide
  have hdescent : baseEnd_5248234 < baseStart_5248234 := by decide
  rcases family_descends (prefixWord ++ tailWord_5248234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5248284 : List Nat := [2, 2, 3, 1, 1, 1, 2, 2, 4, 5]
def baseStart_5248284 : Nat := 118140960795 + 5248284 * 2 ^ 59
def prefixEnd_5248284 : Nat := 4983230072969 + 3 ^ 40 * 5248284 * 2
def baseEnd_5248284 : Nat := 898297434433816432804529

theorem tailTrace_5248284 : CollatzResearch.WordTrace tailWord_5248284 prefixEnd_5248284 898297434433816432804529 := by
  unfold tailWord_5248284
  simp only [CollatzResearch.WordTrace]
  refine ⟨95710321659185439195695953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127613762212247252260927937 95710321659185439195695953)
  ·
    refine ⟨71782741244389079396771965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95710321659185439195695953 71782741244389079396771965)
    ·
      refine ⟨26918527966645904773789487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71782741244389079396771965 26918527966645904773789487)
      ·
        refine ⟨40377791949968857160684231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26918527966645904773789487 40377791949968857160684231)
        ·
          refine ⟨60566687924953285741026347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40377791949968857160684231 60566687924953285741026347)
          ·
            refine ⟨90850031887429928611539521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60566687924953285741026347 90850031887429928611539521)
            ·
              refine ⟨68137523915572446458654641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90850031887429928611539521 68137523915572446458654641)
              ·
                refine ⟨51103142936679334843990981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68137523915572446458654641 51103142936679334843990981)
                ·
                  refine ⟨9581839300627375283248309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51103142936679334843990981 9581839300627375283248309)
                  ·
                    refine ⟨898297434433816432804529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9581839300627375283248309 898297434433816432804529)
                    ·
                      rfl

theorem cell23_5248284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_5248284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5248284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5248284 prefixEnd_5248284 := by exact prefixLift 5248284
  have htrace : WordTrace (prefixWord ++ tailWord_5248284) baseStart_5248284 baseEnd_5248284 := by
    simpa [prefixWord, tailWord_5248284, baseEnd_5248284] using wordTrace_append hprefix tailTrace_5248284
  have hstable : (prefixWord ++ tailWord_5248284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5248284).length < 2 ^ (prefixWord ++ tailWord_5248284).sum := by decide
  have hdescent : baseEnd_5248284 < baseStart_5248284 := by decide
  rcases family_descends (prefixWord ++ tailWord_5248284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5248304 : List Nat := [2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 4]
def baseStart_5248304 : Nat := 118140960795 + 5248304 * 2 ^ 59
def prefixEnd_5248304 : Nat := 4983230072969 + 3 ^ 40 * 5248304 * 2
def baseEnd_5248304 : Nat := 2694902572914539220163495

theorem tailTrace_5248304 : CollatzResearch.WordTrace tailWord_5248304 prefixEnd_5248304 2694902572914539220163495 := by
  unfold tailWord_5248304
  simp only [CollatzResearch.WordTrace]
  refine ⟨95710686389149210903559983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127614248518865614538079977 95710686389149210903559983)
  ·
    refine ⟨143566029583723816355339975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95710686389149210903559983 143566029583723816355339975)
    ·
      refine ⟨215349044375585724533009963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143566029583723816355339975 215349044375585724533009963)
      ·
        refine ⟨323023566563378586799514945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215349044375585724533009963 323023566563378586799514945)
        ·
          refine ⟨242267674922533940099636209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 323023566563378586799514945 242267674922533940099636209)
          ·
            refine ⟨181700756191900455074727157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 242267674922533940099636209 181700756191900455074727157)
            ·
              refine ⟨17034445892990667663255671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 181700756191900455074727157 17034445892990667663255671)
              ·
                refine ⟨25551668839486001494883507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17034445892990667663255671 25551668839486001494883507)
                ·
                  refine ⟨38327503259229002242325261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25551668839486001494883507 38327503259229002242325261)
                  ·
                    refine ⟨14372813722210875840871973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38327503259229002242325261 14372813722210875840871973)
                    ·
                      refine ⟨2694902572914539220163495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14372813722210875840871973 2694902572914539220163495)
                      ·
                        rfl

theorem cell23_5248304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 4].length) (baseStart_5248304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5248304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5248304 prefixEnd_5248304 := by exact prefixLift 5248304
  have htrace : WordTrace (prefixWord ++ tailWord_5248304) baseStart_5248304 baseEnd_5248304 := by
    simpa [prefixWord, tailWord_5248304, baseEnd_5248304] using wordTrace_append hprefix tailTrace_5248304
  have hstable : (prefixWord ++ tailWord_5248304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5248304).length < 2 ^ (prefixWord ++ tailWord_5248304).sum := by decide
  have hdescent : baseEnd_5248304 < baseStart_5248304 := by decide
  rcases family_descends (prefixWord ++ tailWord_5248304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5248334 : List Nat := [4, 1, 1, 1, 1, 1, 3, 2, 2, 1, 6]
def baseStart_5248334 : Nat := 118140960795 + 5248334 * 2 ^ 59
def prefixEnd_5248334 : Nat := 4983230072969 + 3 ^ 40 * 5248334 * 2
def baseEnd_5248334 : Nat := 2694917977334174102788357

theorem tailTrace_5248334 : CollatzResearch.WordTrace tailWord_5248334 prefixEnd_5248334 2694917977334174102788357 := by
  unfold tailWord_5248334
  simp only [CollatzResearch.WordTrace]
  refine ⟨23927808371023717116339007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127614977978793157953808037 23927808371023717116339007)
  ·
    refine ⟨35891712556535575674508511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23927808371023717116339007 35891712556535575674508511)
    ·
      refine ⟨53837568834803363511762767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35891712556535575674508511 53837568834803363511762767)
      ·
        refine ⟨80756353252205045267644151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53837568834803363511762767 80756353252205045267644151)
        ·
          refine ⟨121134529878307567901466227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80756353252205045267644151 121134529878307567901466227)
          ·
            refine ⟨181701794817461351852199341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121134529878307567901466227 181701794817461351852199341)
            ·
              refine ⟨68138173056548006944574753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 181701794817461351852199341 68138173056548006944574753)
              ·
                refine ⟨51103629792411005208431065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68138173056548006944574753 51103629792411005208431065)
                ·
                  refine ⟨38327722344308253906323299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51103629792411005208431065 38327722344308253906323299)
                  ·
                    refine ⟨57491583516462380859484949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38327722344308253906323299 57491583516462380859484949)
                    ·
                      refine ⟨2694917977334174102788357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57491583516462380859484949 2694917977334174102788357)
                      ·
                        rfl

theorem cell23_5248334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_5248334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5248334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5248334 prefixEnd_5248334 := by exact prefixLift 5248334
  have htrace : WordTrace (prefixWord ++ tailWord_5248334) baseStart_5248334 baseEnd_5248334 := by
    simpa [prefixWord, tailWord_5248334, baseEnd_5248334] using wordTrace_append hprefix tailTrace_5248334
  have hstable : (prefixWord ++ tailWord_5248334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5248334).length < 2 ^ (prefixWord ++ tailWord_5248334).sum := by decide
  have hdescent : baseEnd_5248334 < baseStart_5248334 := by decide
  rcases family_descends (prefixWord ++ tailWord_5248334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5248341 : List Nat := [1, 3, 2, 2, 3, 1, 1, 2, 1, 4, 3]
def baseStart_5248341 : Nat := 118140960795 + 5248341 * 2 ^ 59
def prefixEnd_5248341 : Nat := 4983230072969 + 3 ^ 40 * 5248341 * 2
def baseEnd_5248341 : Nat := 2694921571698755575400825

theorem tailTrace_5248341 : CollatzResearch.WordTrace tailWord_5248341 prefixEnd_5248341 2694921571698755575400825 := by
  unfold tailWord_5248341
  simp only [CollatzResearch.WordTrace]
  refine ⟨191422722279164377126216877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127615148186109584750811251 191422722279164377126216877)
  ·
    refine ⟨71783520854686641422331329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191422722279164377126216877 71783520854686641422331329)
    ·
      refine ⟨53837640641014981066748497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71783520854686641422331329 53837640641014981066748497)
      ·
        refine ⟨40378230480761235800061373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53837640641014981066748497 40378230480761235800061373)
        ·
          refine ⟨15141836430285463425023015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40378230480761235800061373 15141836430285463425023015)
          ·
            refine ⟨22712754645428195137534523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15141836430285463425023015 22712754645428195137534523)
            ·
              refine ⟨34069131968142292706301785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22712754645428195137534523 34069131968142292706301785)
              ·
                refine ⟨25551848976106719529726339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34069131968142292706301785 25551848976106719529726339)
                ·
                  refine ⟨38327773464160079294589509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25551848976106719529726339 38327773464160079294589509)
                  ·
                    refine ⟨7186457524530014867735533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38327773464160079294589509 7186457524530014867735533)
                    ·
                      refine ⟨2694921571698755575400825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7186457524530014867735533 2694921571698755575400825)
                      ·
                        rfl

theorem cell23_5248341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_5248341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5248341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5248341 prefixEnd_5248341 := by exact prefixLift 5248341
  have htrace : WordTrace (prefixWord ++ tailWord_5248341) baseStart_5248341 baseEnd_5248341 := by
    simpa [prefixWord, tailWord_5248341, baseEnd_5248341] using wordTrace_append hprefix tailTrace_5248341
  have hstable : (prefixWord ++ tailWord_5248341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5248341).length < 2 ^ (prefixWord ++ tailWord_5248341).sum := by decide
  have hdescent : baseEnd_5248341 < baseStart_5248341 := by decide
  rcases family_descends (prefixWord ++ tailWord_5248341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5248365 : List Nat := [1, 5, 1, 1, 1, 3, 3, 3, 1, 4]
def baseStart_5248365 : Nat := 118140960795 + 5248365 * 2 ^ 59
def prefixEnd_5248365 : Nat := 4983230072969 + 3 ^ 40 * 5248365 * 2
def baseEnd_5248365 : Nat := 898311298411487827166905

theorem tailTrace_5248365 : CollatzResearch.WordTrace tailWord_5248365 prefixEnd_5248365 898311298411487827166905 := by
  unfold tailWord_5248365
  simp only [CollatzResearch.WordTrace]
  refine ⟨191423597631077429225090549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127615731754051619483393699 191423597631077429225090549)
  ·
    refine ⟨17945962277913508989852239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 191423597631077429225090549 17945962277913508989852239)
    ·
      refine ⟨26918943416870263484778359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17945962277913508989852239 26918943416870263484778359)
      ·
        refine ⟨40378415125305395227167539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26918943416870263484778359 40378415125305395227167539)
        ·
          refine ⟨60567622687958092840751309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40378415125305395227167539 60567622687958092840751309)
          ·
            refine ⟨22712858507984284815281741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60567622687958092840751309 22712858507984284815281741)
            ·
              refine ⟨8517321940494106805730653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22712858507984284815281741 8517321940494106805730653)
              ·
                refine ⟨3193995727685290052148995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8517321940494106805730653 3193995727685290052148995)
                ·
                  refine ⟨4790993591527935078223493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3193995727685290052148995 4790993591527935078223493)
                  ·
                    refine ⟨898311298411487827166905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4790993591527935078223493 898311298411487827166905)
                    ·
                      rfl

theorem cell23_5248365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 3, 1, 4].length) (baseStart_5248365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5248365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5248365 prefixEnd_5248365 := by exact prefixLift 5248365
  have htrace : WordTrace (prefixWord ++ tailWord_5248365) baseStart_5248365 baseEnd_5248365 := by
    simpa [prefixWord, tailWord_5248365, baseEnd_5248365] using wordTrace_append hprefix tailTrace_5248365
  have hstable : (prefixWord ++ tailWord_5248365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5248365).length < 2 ^ (prefixWord ++ tailWord_5248365).sum := by decide
  have hdescent : baseEnd_5248365 < baseStart_5248365 := by decide
  rcases family_descends (prefixWord ++ tailWord_5248365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5248408 : List Nat := [2, 1, 2, 5, 2, 1, 1, 1, 3, 5]
def baseStart_5248408 : Nat := 118140960795 + 5248408 * 2 ^ 59
def prefixEnd_5248408 : Nat := 4983230072969 + 3 ^ 40 * 5248408 * 2
def baseEnd_5248408 : Nat := 898318658300868937754339

theorem tailTrace_5248408 : CollatzResearch.WordTrace tailWord_5248408 prefixEnd_5248408 898318658300868937754339 := by
  unfold tailWord_5248408
  simp only [CollatzResearch.WordTrace]
  refine ⟨95712582984960823784452939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127616777313281098379270585 95712582984960823784452939)
  ·
    refine ⟨143568874477441235676679409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95712582984960823784452939 143568874477441235676679409)
    ·
      refine ⟨107676655858080926757509557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143568874477441235676679409 107676655858080926757509557)
      ·
        refine ⟨10094686486695086883516521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 107676655858080926757509557 10094686486695086883516521)
        ·
          refine ⟨7571014865021315162637391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10094686486695086883516521 7571014865021315162637391)
          ·
            refine ⟨11356522297531972743956087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7571014865021315162637391 11356522297531972743956087)
            ·
              refine ⟨17034783446297959115934131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11356522297531972743956087 17034783446297959115934131)
              ·
                refine ⟨25552175169446938673901197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17034783446297959115934131 25552175169446938673901197)
                ·
                  refine ⟨9582065688542602002712949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25552175169446938673901197 9582065688542602002712949)
                  ·
                    refine ⟨898318658300868937754339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9582065688542602002712949 898318658300868937754339)
                    ·
                      rfl

theorem cell23_5248408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 3, 5].length) (baseStart_5248408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5248408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5248408 prefixEnd_5248408 := by exact prefixLift 5248408
  have htrace : WordTrace (prefixWord ++ tailWord_5248408) baseStart_5248408 baseEnd_5248408 := by
    simpa [prefixWord, tailWord_5248408, baseEnd_5248408] using wordTrace_append hprefix tailTrace_5248408
  have hstable : (prefixWord ++ tailWord_5248408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5248408).length < 2 ^ (prefixWord ++ tailWord_5248408).sum := by decide
  have hdescent : baseEnd_5248408 < baseStart_5248408 := by decide
  rcases family_descends (prefixWord ++ tailWord_5248408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5248415 : List Nat := [1, 1, 2, 5, 1, 3, 2, 1, 2, 3, 2]
def baseStart_5248415 : Nat := 118140960795 + 5248415 * 2 ^ 59
def prefixEnd_5248415 : Nat := 4983230072969 + 3 ^ 40 * 5248415 * 2
def baseEnd_5248415 : Nat := 2694959569267188285875485

theorem tailTrace_5248415 : CollatzResearch.WordTrace tailWord_5248415 prefixEnd_5248415 2694959569267188285875485 := by
  unfold tailWord_5248415
  simp only [CollatzResearch.WordTrace]
  refine ⟨191425421280896287764410699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127616947520597525176273799 191425421280896287764410699)
  ·
    refine ⟨287138131921344431646616049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191425421280896287764410699 287138131921344431646616049)
    ·
      refine ⟨215353598941008323734962037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287138131921344431646616049 215353598941008323734962037)
      ·
        refine ⟨20189399900719530350152691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 215353598941008323734962037 20189399900719530350152691)
        ·
          refine ⟨30284099851079295525229037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20189399900719530350152691 30284099851079295525229037)
          ·
            refine ⟨11356537444154735821960889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30284099851079295525229037 11356537444154735821960889)
            ·
              refine ⟨8517403083116051866470667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11356537444154735821960889 8517403083116051866470667)
              ·
                refine ⟨12776104624674077799706001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8517403083116051866470667 12776104624674077799706001)
                ·
                  refine ⟨9582078468505558349779501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12776104624674077799706001 9582078468505558349779501)
                  ·
                    refine ⟨3593279425689584381167313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9582078468505558349779501 3593279425689584381167313)
                    ·
                      refine ⟨2694959569267188285875485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3593279425689584381167313 2694959569267188285875485)
                      ·
                        rfl

theorem cell23_5248415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_5248415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5248415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5248415 prefixEnd_5248415 := by exact prefixLift 5248415
  have htrace : WordTrace (prefixWord ++ tailWord_5248415) baseStart_5248415 baseEnd_5248415 := by
    simpa [prefixWord, tailWord_5248415, baseEnd_5248415] using wordTrace_append hprefix tailTrace_5248415
  have hstable : (prefixWord ++ tailWord_5248415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5248415).length < 2 ^ (prefixWord ++ tailWord_5248415).sum := by decide
  have hdescent : baseEnd_5248415 < baseStart_5248415 := by decide
  rcases family_descends (prefixWord ++ tailWord_5248415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5248421 : List Nat := [1, 3, 1, 2, 1, 1, 2, 4, 4, 4]
def baseStart_5248421 : Nat := 118140960795 + 5248421 * 2 ^ 59
def prefixEnd_5248421 : Nat := 4983230072969 + 3 ^ 40 * 5248421 * 2
def baseEnd_5248421 : Nat := 898320883383705087466819

theorem tailTrace_5248421 : CollatzResearch.WordTrace tailWord_5248421 prefixEnd_5248421 898320883383705087466819 := by
  unfold tailWord_5248421
  simp only [CollatzResearch.WordTrace]
  refine ⟨191425640118874550789129117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127617093412583033859419411 191425640118874550789129117)
  ·
    refine ⟨71784615044577956545923419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191425640118874550789129117 71784615044577956545923419)
    ·
      refine ⟨107676922566866934818885129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71784615044577956545923419 107676922566866934818885129)
      ·
        refine ⟨80757691925150201114163847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107676922566866934818885129 80757691925150201114163847)
        ·
          refine ⟨121136537887725301671245771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80757691925150201114163847 121136537887725301671245771)
          ·
            refine ⟨181704806831587952506868657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121136537887725301671245771 181704806831587952506868657)
            ·
              refine ⟨136278605123690964380151493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 181704806831587952506868657 136278605123690964380151493)
              ·
                refine ⟨25552238460692055821278405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 136278605123690964380151493 25552238460692055821278405)
                ·
                  refine ⟨4791044711379760466489701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25552238460692055821278405 4791044711379760466489701)
                  ·
                    refine ⟨898320883383705087466819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4791044711379760466489701 898320883383705087466819)
                    ·
                      rfl

theorem cell23_5248421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 4, 4].length) (baseStart_5248421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5248421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5248421 prefixEnd_5248421 := by exact prefixLift 5248421
  have htrace : WordTrace (prefixWord ++ tailWord_5248421) baseStart_5248421 baseEnd_5248421 := by
    simpa [prefixWord, tailWord_5248421, baseEnd_5248421] using wordTrace_append hprefix tailTrace_5248421
  have hstable : (prefixWord ++ tailWord_5248421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5248421).length < 2 ^ (prefixWord ++ tailWord_5248421).sum := by decide
  have hdescent : baseEnd_5248421 < baseStart_5248421 := by decide
  rcases family_descends (prefixWord ++ tailWord_5248421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5248445 : List Nat := [1, 4, 1, 2, 2, 1, 2, 3, 3, 2, 2]
def baseStart_5248445 : Nat := 118140960795 + 5248445 * 2 ^ 59
def prefixEnd_5248445 : Nat := 4983230072969 + 3 ^ 40 * 5248445 * 2
def baseEnd_5248445 : Nat := 2694974973686823168500347

theorem tailTrace_5248445 : CollatzResearch.WordTrace tailWord_5248445 prefixEnd_5248445 2694974973686823168500347 := by
  unfold tailWord_5248445
  simp only [CollatzResearch.WordTrace]
  refine ⟨191426515470787602888002789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127617676980525068592001859 191426515470787602888002789)
  ·
    refine ⟨35892471650772675541500523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 191426515470787602888002789 35892471650772675541500523)
    ·
      refine ⟨53838707476159013312250785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35892471650772675541500523 53838707476159013312250785)
      ·
        refine ⟨40379030607119259984188089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53838707476159013312250785 40379030607119259984188089)
        ·
          refine ⟨30284272955339444988141067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40379030607119259984188089 30284272955339444988141067)
          ·
            refine ⟨45426409433009167482211601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30284272955339444988141067 45426409433009167482211601)
            ·
              refine ⟨34069807074756875611658701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45426409433009167482211601 34069807074756875611658701)
              ·
                refine ⟨12776177653033828354372013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34069807074756875611658701 12776177653033828354372013)
                ·
                  refine ⟨4791066619887685632889505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12776177653033828354372013 4791066619887685632889505)
                  ·
                    refine ⟨3593299964915764224667129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4791066619887685632889505 3593299964915764224667129)
                    ·
                      refine ⟨2694974973686823168500347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3593299964915764224667129 2694974973686823168500347)
                      ·
                        rfl

theorem cell23_5248445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 3, 3, 2, 2].length) (baseStart_5248445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5248445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5248445 prefixEnd_5248445 := by exact prefixLift 5248445
  have htrace : WordTrace (prefixWord ++ tailWord_5248445) baseStart_5248445 baseEnd_5248445 := by
    simpa [prefixWord, tailWord_5248445, baseEnd_5248445] using wordTrace_append hprefix tailTrace_5248445
  have hstable : (prefixWord ++ tailWord_5248445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5248445).length < 2 ^ (prefixWord ++ tailWord_5248445).sum := by decide
  have hdescent : baseEnd_5248445 < baseStart_5248445 := by decide
  rcases family_descends (prefixWord ++ tailWord_5248445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5248458 : List Nat := [3, 1, 2, 1, 2, 4, 2, 1, 1, 2, 4]
def baseStart_5248458 : Nat := 118140960795 + 5248458 * 2 ^ 59
def prefixEnd_5248458 : Nat := 4983230072969 + 3 ^ 40 * 5248458 * 2
def baseEnd_5248458 : Nat := 2694981648935331617637787

theorem tailTrace_5248458 : CollatzResearch.WordTrace tailWord_5248458 prefixEnd_5248458 2694981648935331617637787 := by
  unfold tailWord_5248458
  simp only [CollatzResearch.WordTrace]
  refine ⟨47856747404935126527056507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127617993079827004072150685 47856747404935126527056507)
  ·
    refine ⟨71785121107402689790584761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47856747404935126527056507 71785121107402689790584761)
    ·
      refine ⟨53838840830552017342938571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71785121107402689790584761 53838840830552017342938571)
      ·
        refine ⟨80758261245828026014407857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53838840830552017342938571 80758261245828026014407857)
        ·
          refine ⟨60568695934371019510805893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80758261245828026014407857 60568695934371019510805893)
          ·
            refine ⟨11356630487694566158276105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60568695934371019510805893 11356630487694566158276105)
            ·
              refine ⟨8517472865770924618707079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11356630487694566158276105 8517472865770924618707079)
              ·
                refine ⟨12776209298656386928060619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8517472865770924618707079 12776209298656386928060619)
                ·
                  refine ⟨19164313947984580392090929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12776209298656386928060619 19164313947984580392090929)
                  ·
                    refine ⟨14373235460988435294068197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19164313947984580392090929 14373235460988435294068197)
                    ·
                      refine ⟨2694981648935331617637787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14373235460988435294068197 2694981648935331617637787)
                      ·
                        rfl

theorem cell23_5248458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 1, 1, 2, 4].length) (baseStart_5248458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5248458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5248458 prefixEnd_5248458 := by exact prefixLift 5248458
  have htrace : WordTrace (prefixWord ++ tailWord_5248458) baseStart_5248458 baseEnd_5248458 := by
    simpa [prefixWord, tailWord_5248458, baseEnd_5248458] using wordTrace_append hprefix tailTrace_5248458
  have hstable : (prefixWord ++ tailWord_5248458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5248458).length < 2 ^ (prefixWord ++ tailWord_5248458).sum := by decide
  have hdescent : baseEnd_5248458 < baseStart_5248458 := by decide
  rcases family_descends (prefixWord ++ tailWord_5248458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5248495 : List Nat := [1, 1, 2, 1, 4, 1, 5, 2, 2, 1, 3]
def baseStart_5248495 : Nat := 118140960795 + 5248495 * 2 ^ 59
def prefixEnd_5248495 : Nat := 4983230072969 + 3 ^ 40 * 5248495 * 2
def baseEnd_5248495 : Nat := 2695000647719547972875117

theorem tailTrace_5248495 : CollatzResearch.WordTrace tailWord_5248495 prefixEnd_5248495 2695000647719547972875117 := by
  unfold tailWord_5248495
  simp only [CollatzResearch.WordTrace]
  refine ⟨191428339120606461427322939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127618892747070974284881959 191428339120606461427322939)
  ·
    refine ⟨287142508680909692140984409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191428339120606461427322939 287142508680909692140984409)
    ·
      refine ⟨215356881510682269105738307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287142508680909692140984409 215356881510682269105738307)
      ·
        refine ⟨323035322266023403658607461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215356881510682269105738307 323035322266023403658607461)
        ·
          refine ⟨60569122924879388185988899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 323035322266023403658607461 60569122924879388185988899)
          ·
            refine ⟨90853684387319082278983349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60569122924879388185988899 90853684387319082278983349)
            ·
              refine ⟨8517532911311163963654689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 90853684387319082278983349 8517532911311163963654689)
              ·
                refine ⟨6388149683483372972741017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8517532911311163963654689 6388149683483372972741017)
                ·
                  refine ⟨4791112262612529729555763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6388149683483372972741017 4791112262612529729555763)
                  ·
                    refine ⟨7186668393918794594333645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4791112262612529729555763 7186668393918794594333645)
                    ·
                      refine ⟨2695000647719547972875117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7186668393918794594333645 2695000647719547972875117)
                      ·
                        rfl

theorem cell23_5248495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 2, 2, 1, 3].length) (baseStart_5248495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5248495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5248495 prefixEnd_5248495 := by exact prefixLift 5248495
  have htrace : WordTrace (prefixWord ++ tailWord_5248495) baseStart_5248495 baseEnd_5248495 := by
    simpa [prefixWord, tailWord_5248495, baseEnd_5248495] using wordTrace_append hprefix tailTrace_5248495
  have hstable : (prefixWord ++ tailWord_5248495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5248495).length < 2 ^ (prefixWord ++ tailWord_5248495).sum := by decide
  have hdescent : baseEnd_5248495 < baseStart_5248495 := by decide
  rcases family_descends (prefixWord ++ tailWord_5248495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5248521 : List Nat := [1, 2, 1, 1, 3, 1, 4, 2, 2, 1, 5]
def baseStart_5248521 : Nat := 118140960795 + 5248521 * 2 ^ 59
def prefixEnd_5248521 : Nat := 4983230072969 + 3 ^ 40 * 5248521 * 2
def baseEnd_5248521 : Nat := 2695013998216564871149997

theorem tailTrace_5248521 : CollatzResearch.WordTrace tailWord_5248521 prefixEnd_5248521 2695013998216564871149997 := by
  unfold tailWord_5248521
  simp only [CollatzResearch.WordTrace]
  refine ⟨191429287418512267867769417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127619524945674845245179611 191429287418512267867769417)
  ·
    refine ⟨143571965563884200900827063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191429287418512267867769417 143571965563884200900827063)
    ·
      refine ⟨215357948345826301351240595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143571965563884200900827063 215357948345826301351240595)
      ·
        refine ⟨323036922518739452026860893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215357948345826301351240595 323036922518739452026860893)
        ·
          refine ⟨121138845944527294510072835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 323036922518739452026860893 121138845944527294510072835)
          ·
            refine ⟨181708268916790941765109253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121138845944527294510072835 181708268916790941765109253)
            ·
              refine ⟨34070300421898301580957985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 181708268916790941765109253 34070300421898301580957985)
              ·
                refine ⟨25552725316423726185718489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34070300421898301580957985 25552725316423726185718489)
                ·
                  refine ⟨19164543987317794639288867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25552725316423726185718489 19164543987317794639288867)
                  ·
                    refine ⟨28746815980976691958933301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19164543987317794639288867 28746815980976691958933301)
                    ·
                      refine ⟨2695013998216564871149997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28746815980976691958933301 2695013998216564871149997)
                      ·
                        rfl

theorem cell23_5248521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 2, 1, 5].length) (baseStart_5248521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5248521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5248521 prefixEnd_5248521 := by exact prefixLift 5248521
  have htrace : WordTrace (prefixWord ++ tailWord_5248521) baseStart_5248521 baseEnd_5248521 := by
    simpa [prefixWord, tailWord_5248521, baseEnd_5248521] using wordTrace_append hprefix tailTrace_5248521
  have hstable : (prefixWord ++ tailWord_5248521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5248521).length < 2 ^ (prefixWord ++ tailWord_5248521).sum := by decide
  have hdescent : baseEnd_5248521 < baseStart_5248521 := by decide
  rcases family_descends (prefixWord ++ tailWord_5248521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5248522 : List Nat := [3, 1, 2, 2, 2, 3, 2, 2, 1, 3, 2]
def baseStart_5248522 : Nat := 118140960795 + 5248522 * 2 ^ 59
def prefixEnd_5248522 : Nat := 4983230072969 + 3 ^ 40 * 5248522 * 2
def baseEnd_5248522 : Nat := 2695014511697219367237493

theorem tailTrace_5248522 : CollatzResearch.WordTrace tailWord_5248522 prefixEnd_5248522 2695014511697219367237493 := by
  unfold tailWord_5248522
  simp only [CollatzResearch.WordTrace]
  refine ⟨47857330972877161259638955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127619549261005763359037213 47857330972877161259638955)
  ·
    refine ⟨71785996459315741889458433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47857330972877161259638955 71785996459315741889458433)
    ·
      refine ⟨53839497344486806417093825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71785996459315741889458433 53839497344486806417093825)
      ·
        refine ⟨40379623008365104812820369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53839497344486806417093825 40379623008365104812820369)
        ·
          refine ⟨30284717256273828609615277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40379623008365104812820369 30284717256273828609615277)
          ·
            refine ⟨11356768971102685728605729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30284717256273828609615277 11356768971102685728605729)
            ·
              refine ⟨8517576728327014296454297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11356768971102685728605729 8517576728327014296454297)
              ·
                refine ⟨6388182546245260722340723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8517576728327014296454297 6388182546245260722340723)
                ·
                  refine ⟨9582273819367891083511085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6388182546245260722340723 9582273819367891083511085)
                  ·
                    refine ⟨3593352682262959156316657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9582273819367891083511085 3593352682262959156316657)
                    ·
                      refine ⟨2695014511697219367237493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3593352682262959156316657 2695014511697219367237493)
                      ·
                        rfl

theorem cell23_5248522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 2, 1, 3, 2].length) (baseStart_5248522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5248522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5248522 prefixEnd_5248522 := by exact prefixLift 5248522
  have htrace : WordTrace (prefixWord ++ tailWord_5248522) baseStart_5248522 baseEnd_5248522 := by
    simpa [prefixWord, tailWord_5248522, baseEnd_5248522] using wordTrace_append hprefix tailTrace_5248522
  have hstable : (prefixWord ++ tailWord_5248522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5248522).length < 2 ^ (prefixWord ++ tailWord_5248522).sum := by decide
  have hdescent : baseEnd_5248522 < baseStart_5248522 := by decide
  rcases family_descends (prefixWord ++ tailWord_5248522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5248569 : List Nat := [1, 2, 1, 5, 1, 2, 4, 1, 2, 2, 2]
def baseStart_5248569 : Nat := 118140960795 + 5248569 * 2 ^ 59
def prefixEnd_5248569 : Nat := 4983230072969 + 3 ^ 40 * 5248569 * 2
def baseEnd_5248569 : Nat := 2695038645287980683349777

theorem tailTrace_5248569 : CollatzResearch.WordTrace tailWord_5248569 prefixEnd_5248569 2695038645287980683349777 := by
  unfold tailWord_5248569
  simp only [CollatzResearch.WordTrace]
  refine ⟨191431038122338372065516761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127620692081558914710344507 191431038122338372065516761)
  ·
    refine ⟨143573278591753779049137571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191431038122338372065516761 143573278591753779049137571)
    ·
      refine ⟨215359917887630668573706357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143573278591753779049137571 215359917887630668573706357)
      ·
        refine ⟨20189992301965375178784971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 215359917887630668573706357 20189992301965375178784971)
        ·
          refine ⟨30284988452948062768177457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20189992301965375178784971 30284988452948062768177457)
          ·
            refine ⟨22713741339711047076133093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30284988452948062768177457 22713741339711047076133093)
            ·
              refine ⟨4258826501195821326774955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22713741339711047076133093 4258826501195821326774955)
              ·
                refine ⟨6388239751793731990162433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4258826501195821326774955 6388239751793731990162433)
                ·
                  refine ⟨4791179813845298992621825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6388239751793731990162433 4791179813845298992621825)
                  ·
                    refine ⟨3593384860383974244466369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4791179813845298992621825 3593384860383974244466369)
                    ·
                      refine ⟨2695038645287980683349777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3593384860383974244466369 2695038645287980683349777)
                      ·
                        rfl

theorem cell23_5248569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_5248569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5248569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5248569 prefixEnd_5248569 := by exact prefixLift 5248569
  have htrace : WordTrace (prefixWord ++ tailWord_5248569) baseStart_5248569 baseEnd_5248569 := by
    simpa [prefixWord, tailWord_5248569, baseEnd_5248569] using wordTrace_append hprefix tailTrace_5248569
  have hstable : (prefixWord ++ tailWord_5248569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5248569).length < 2 ^ (prefixWord ++ tailWord_5248569).sum := by decide
  have hdescent : baseEnd_5248569 < baseStart_5248569 := by decide
  rcases family_descends (prefixWord ++ tailWord_5248569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5248581 : List Nat := [1, 3, 1, 1, 1, 4, 1, 2, 1, 1, 7]
def baseStart_5248581 : Nat := 118140960795 + 5248581 * 2 ^ 59
def prefixEnd_5248581 : Nat := 4983230072969 + 3 ^ 40 * 5248581 * 2
def baseEnd_5248581 : Nat := 2695044807055834636399721

theorem tailTrace_5248581 : CollatzResearch.WordTrace tailWord_5248581 prefixEnd_5248581 2695044807055834636399721 := by
  unfold tailWord_5248581
  simp only [CollatzResearch.WordTrace]
  refine ⟨191431475798294898114953597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127620983865529932076635731 191431475798294898114953597)
  ·
    refine ⟨71786803424360586793107599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191431475798294898114953597 71786803424360586793107599)
    ·
      refine ⟨107680205136540880189661399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71786803424360586793107599 107680205136540880189661399)
      ·
        refine ⟨161520307704811320284492099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107680205136540880189661399 161520307704811320284492099)
        ·
          refine ⟨242280461557216980426738149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161520307704811320284492099 242280461557216980426738149)
          ·
            refine ⟨45427586541978183830013403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 242280461557216980426738149 45427586541978183830013403)
            ·
              refine ⟨68141379812967275745020105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45427586541978183830013403 68141379812967275745020105)
              ·
                refine ⟨51106034859725456808765079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68141379812967275745020105 51106034859725456808765079)
                ·
                  refine ⟨76659052289588185213147619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51106034859725456808765079 76659052289588185213147619)
                  ·
                    refine ⟨114988578434382277819721429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 76659052289588185213147619 114988578434382277819721429)
                    ·
                      refine ⟨2695044807055834636399721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 114988578434382277819721429 2695044807055834636399721)
                      ·
                        rfl

theorem cell23_5248581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 1, 7].length) (baseStart_5248581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5248581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5248581 prefixEnd_5248581 := by exact prefixLift 5248581
  have htrace : WordTrace (prefixWord ++ tailWord_5248581) baseStart_5248581 baseEnd_5248581 := by
    simpa [prefixWord, tailWord_5248581, baseEnd_5248581] using wordTrace_append hprefix tailTrace_5248581
  have hstable : (prefixWord ++ tailWord_5248581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5248581).length < 2 ^ (prefixWord ++ tailWord_5248581).sum := by decide
  have hdescent : baseEnd_5248581 < baseStart_5248581 := by decide
  rcases family_descends (prefixWord ++ tailWord_5248581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5248588 : List Nat := [2, 2, 1, 3, 1, 3, 1, 3, 2, 5]
def baseStart_5248588 : Nat := 118140960795 + 5248588 * 2 ^ 59
def prefixEnd_5248588 : Nat := 4983230072969 + 3 ^ 40 * 5248588 * 2
def baseEnd_5248588 : Nat := 898349467140138703004063

theorem tailTrace_5248588 : CollatzResearch.WordTrace tailWord_5248588 prefixEnd_5248588 898349467140138703004063 := by
  unfold tailWord_5248588
  simp only [CollatzResearch.WordTrace]
  refine ⟨95715865554634769155229209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127621154072846358873638945 95715865554634769155229209)
  ·
    refine ⟨71786899165976076866421907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95715865554634769155229209 71786899165976076866421907)
    ·
      refine ⟨107680348748964115299632861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71786899165976076866421907 107680348748964115299632861)
      ·
        refine ⟨40380130780861543237362323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107680348748964115299632861 40380130780861543237362323)
        ·
          refine ⟨60570196171292314856043485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40380130780861543237362323 60570196171292314856043485)
          ·
            refine ⟨22713823564234618071016307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60570196171292314856043485 22713823564234618071016307)
            ·
              refine ⟨34070735346351927106524461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22713823564234618071016307 34070735346351927106524461)
              ·
                refine ⟨12776525754881972664946673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34070735346351927106524461 12776525754881972664946673)
                ·
                  refine ⟨9582394316161479498710005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12776525754881972664946673 9582394316161479498710005)
                  ·
                    refine ⟨898349467140138703004063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9582394316161479498710005 898349467140138703004063)
                    ·
                      rfl

theorem cell23_5248588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 3, 2, 5].length) (baseStart_5248588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5248588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5248588 prefixEnd_5248588 := by exact prefixLift 5248588
  have htrace : WordTrace (prefixWord ++ tailWord_5248588) baseStart_5248588 baseEnd_5248588 := by
    simpa [prefixWord, tailWord_5248588, baseEnd_5248588] using wordTrace_append hprefix tailTrace_5248588
  have hstable : (prefixWord ++ tailWord_5248588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5248588).length < 2 ^ (prefixWord ++ tailWord_5248588).sum := by decide
  have hdescent : baseEnd_5248588 < baseStart_5248588 := by decide
  rcases family_descends (prefixWord ++ tailWord_5248588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5248631 : List Nat := [1, 1, 3, 1, 1, 3, 1, 2, 10]
def baseStart_5248631 : Nat := 118140960795 + 5248631 * 2 ^ 59
def prefixEnd_5248631 : Nat := 4983230072969 + 3 ^ 40 * 5248631 * 2
def baseEnd_5248631 : Nat := 299452275676506604530499

theorem tailTrace_5248631 : CollatzResearch.WordTrace tailWord_5248631 prefixEnd_5248631 299452275676506604530499 := by
  unfold tailWord_5248631
  simp only [CollatzResearch.WordTrace]
  refine ⟨191433299448113756654273747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127622199632075837769515831 191433299448113756654273747)
  ·
    refine ⟨287149949172170634981410621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191433299448113756654273747 287149949172170634981410621)
    ·
      refine ⟨107681230939563988118028983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 287149949172170634981410621 107681230939563988118028983)
      ·
        refine ⟨161521846409345982177043475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107681230939563988118028983 161521846409345982177043475)
        ·
          refine ⟨242282769614018973265565213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161521846409345982177043475 242282769614018973265565213)
          ·
            refine ⟨90856038605257114974586955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 242282769614018973265565213 90856038605257114974586955)
            ·
              refine ⟨136284057907885672461880433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90856038605257114974586955 136284057907885672461880433)
              ·
                refine ⟨102213043430914254346410325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136284057907885672461880433 102213043430914254346410325)
                ·
                  refine ⟨299452275676506604530499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 102213043430914254346410325 299452275676506604530499)
                  ·
                    rfl

theorem cell23_5248631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 10].length) (baseStart_5248631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5248631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5248631 prefixEnd_5248631 := by exact prefixLift 5248631
  have htrace : WordTrace (prefixWord ++ tailWord_5248631) baseStart_5248631 baseEnd_5248631 := by
    simpa [prefixWord, tailWord_5248631, baseEnd_5248631] using wordTrace_append hprefix tailTrace_5248631
  have hstable : (prefixWord ++ tailWord_5248631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5248631).length < 2 ^ (prefixWord ++ tailWord_5248631).sum := by decide
  have hdescent : baseEnd_5248631 < baseStart_5248631 := by decide
  rcases family_descends (prefixWord ++ tailWord_5248631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5248652 : List Nat := [2, 2, 1, 2, 1, 1, 6, 3, 1, 4]
def baseStart_5248652 : Nat := 118140960795 + 5248652 * 2 ^ 59
def prefixEnd_5248652 : Nat := 4983230072969 + 3 ^ 40 * 5248652 * 2
def baseEnd_5248652 : Nat := 898360421394101286203965

theorem tailTrace_5248652 : CollatzResearch.WordTrace tailWord_5248652 prefixEnd_5248652 898360421394101286203965 := by
  unfold tailWord_5248652
  simp only [CollatzResearch.WordTrace]
  refine ⟨95717032690518838620394105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127622710254025118160525473 95717032690518838620394105)
  ·
    refine ⟨71787774517889128965295579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95717032690518838620394105 71787774517889128965295579)
    ·
      refine ⟨107681661776833693447943369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71787774517889128965295579 107681661776833693447943369)
      ·
        refine ⟨80761246332625270085957527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107681661776833693447943369 80761246332625270085957527)
        ·
          refine ⟨121141869498937905128936291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80761246332625270085957527 121141869498937905128936291)
          ·
            refine ⟨181712804248406857693404437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121141869498937905128936291 181712804248406857693404437)
            ·
              refine ⟨8517787699144071454378333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 181712804248406857693404437 8517787699144071454378333)
              ·
                refine ⟨3194170387179026795391875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8517787699144071454378333 3194170387179026795391875)
                ·
                  refine ⟨4791255580768540193087813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3194170387179026795391875 4791255580768540193087813)
                  ·
                    refine ⟨898360421394101286203965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4791255580768540193087813 898360421394101286203965)
                    ·
                      rfl

theorem cell23_5248652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 3, 1, 4].length) (baseStart_5248652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5248652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5248652 prefixEnd_5248652 := by exact prefixLift 5248652
  have htrace : WordTrace (prefixWord ++ tailWord_5248652) baseStart_5248652 baseEnd_5248652 := by
    simpa [prefixWord, tailWord_5248652, baseEnd_5248652] using wordTrace_append hprefix tailTrace_5248652
  have hstable : (prefixWord ++ tailWord_5248652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5248652).length < 2 ^ (prefixWord ++ tailWord_5248652).sum := by decide
  have hdescent : baseEnd_5248652 < baseStart_5248652 := by decide
  rcases family_descends (prefixWord ++ tailWord_5248652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5248695 : List Nat := [1, 1, 3, 1, 5, 1, 1, 4, 1, 5]
def baseStart_5248695 : Nat := 118140960795 + 5248695 * 2 ^ 59
def prefixEnd_5248695 : Nat := 4983230072969 + 3 ^ 40 * 5248695 * 2
def baseEnd_5248695 : Nat := 898367781283482396791399

theorem tailTrace_5248695 : CollatzResearch.WordTrace tailWord_5248695 prefixEnd_5248695 898367781283482396791399 := by
  unfold tailWord_5248695
  simp only [CollatzResearch.WordTrace]
  refine ⟨191435633719881895584603539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127623755813254597056402359 191435633719881895584603539)
  ·
    refine ⟨287153450579822843376905309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191435633719881895584603539 287153450579822843376905309)
    ·
      refine ⟨107682543967433566266339491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 287153450579822843376905309 107682543967433566266339491)
      ·
        refine ⟨161523815951150349399509237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107682543967433566266339491 161523815951150349399509237)
        ·
          refine ⟨15142857745420345256203991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 161523815951150349399509237 15142857745420345256203991)
          ·
            refine ⟨22714286618130517884305987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15142857745420345256203991 22714286618130517884305987)
            ·
              refine ⟨34071429927195776826458981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22714286618130517884305987 34071429927195776826458981)
              ·
                refine ⟨6388393111349208154961059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34071429927195776826458981 6388393111349208154961059)
                ·
                  refine ⟨9582589667023812232441589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6388393111349208154961059 9582589667023812232441589)
                  ·
                    refine ⟨898367781283482396791399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9582589667023812232441589 898367781283482396791399)
                    ·
                      rfl

theorem cell23_5248695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 4, 1, 5].length) (baseStart_5248695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5248695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5248695 prefixEnd_5248695 := by exact prefixLift 5248695
  have htrace : WordTrace (prefixWord ++ tailWord_5248695) baseStart_5248695 baseEnd_5248695 := by
    simpa [prefixWord, tailWord_5248695, baseEnd_5248695] using wordTrace_append hprefix tailTrace_5248695
  have hstable : (prefixWord ++ tailWord_5248695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5248695).length < 2 ^ (prefixWord ++ tailWord_5248695).sum := by decide
  have hdescent : baseEnd_5248695 < baseStart_5248695 := by decide
  rcases family_descends (prefixWord ++ tailWord_5248695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5248702 : List Nat := [4, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2]
def baseStart_5248702 : Nat := 118140960795 + 5248702 * 2 ^ 59
def prefixEnd_5248702 : Nat := 4983230072969 + 3 ^ 40 * 5248702 * 2
def baseEnd_5248702 : Nat := 2695106938215028662986665

theorem tailTrace_5248702 : CollatzResearch.WordTrace tailWord_5248702 prefixEnd_5248702 2695106938215028662986665 := by
  unfold tailWord_5248702
  simp only [CollatzResearch.WordTrace]
  refine ⟨23929486128857066972513545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127623926020571023853405573 23929486128857066972513545)
  ·
    refine ⟨17947114596642800229385159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23929486128857066972513545 17947114596642800229385159)
    ·
      refine ⟨26920671894964200344077739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17947114596642800229385159 26920671894964200344077739)
      ·
        refine ⟨40381007842446300516116609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26920671894964200344077739 40381007842446300516116609)
        ·
          refine ⟨30285755881834725387087457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40381007842446300516116609 30285755881834725387087457)
          ·
            refine ⟨22714316911376044040315593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30285755881834725387087457 22714316911376044040315593)
            ·
              refine ⟨17035737683532033030236695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22714316911376044040315593 17035737683532033030236695)
              ·
                refine ⟨25553606525298049545355043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17035737683532033030236695 25553606525298049545355043)
                ·
                  refine ⟨38330409787947074318032565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25553606525298049545355043 38330409787947074318032565)
                  ·
                    refine ⟨3593475917620038217315553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38330409787947074318032565 3593475917620038217315553)
                    ·
                      refine ⟨2695106938215028662986665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3593475917620038217315553 2695106938215028662986665)
                      ·
                        rfl

theorem cell23_5248702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2].length) (baseStart_5248702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5248702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5248702 prefixEnd_5248702 := by exact prefixLift 5248702
  have htrace : WordTrace (prefixWord ++ tailWord_5248702) baseStart_5248702 baseEnd_5248702 := by
    simpa [prefixWord, tailWord_5248702, baseEnd_5248702] using wordTrace_append hprefix tailTrace_5248702
  have hstable : (prefixWord ++ tailWord_5248702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5248702).length < 2 ^ (prefixWord ++ tailWord_5248702).sum := by decide
  have hdescent : baseEnd_5248702 < baseStart_5248702 := by decide
  rcases family_descends (prefixWord ++ tailWord_5248702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5248728 : List Nat := [2, 1, 2, 2, 3, 1, 1, 1, 3, 1, 6]
def baseStart_5248728 : Nat := 118140960795 + 5248728 * 2 ^ 59
def prefixEnd_5248728 : Nat := 4983230072969 + 3 ^ 40 * 5248728 * 2
def baseEnd_5248728 : Nat := 2695120288712045561261545

theorem tailTrace_5248728 : CollatzResearch.WordTrace tailWord_5248728 prefixEnd_5248728 2695120288712045561261545 := by
  unfold tailWord_5248728
  simp only [CollatzResearch.WordTrace]
  refine ⟨95718418664381171110277419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127624558219174894813703225 95718418664381171110277419)
  ·
    refine ⟨143577627996571756665416129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95718418664381171110277419 143577627996571756665416129)
    ·
      refine ⟨107683220997428817499062097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143577627996571756665416129 107683220997428817499062097)
      ·
        refine ⟨80762415748071613124296573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107683220997428817499062097 80762415748071613124296573)
        ·
          refine ⟨30285905905526854921611215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80762415748071613124296573 30285905905526854921611215)
          ·
            refine ⟨45428858858290282382416823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30285905905526854921611215 45428858858290282382416823)
            ·
              refine ⟨68143288287435423573625235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45428858858290282382416823 68143288287435423573625235)
              ·
                refine ⟨102214932431153135360437853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68143288287435423573625235 102214932431153135360437853)
                ·
                  refine ⟨38330599661682425760164195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102214932431153135360437853 38330599661682425760164195)
                  ·
                    refine ⟨57495899492523638640246293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38330599661682425760164195 57495899492523638640246293)
                    ·
                      refine ⟨2695120288712045561261545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57495899492523638640246293 2695120288712045561261545)
                      ·
                        rfl

theorem cell23_5248728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_5248728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5248728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5248728 prefixEnd_5248728 := by exact prefixLift 5248728
  have htrace : WordTrace (prefixWord ++ tailWord_5248728) baseStart_5248728 baseEnd_5248728 := by
    simpa [prefixWord, tailWord_5248728, baseEnd_5248728] using wordTrace_append hprefix tailTrace_5248728
  have hstable : (prefixWord ++ tailWord_5248728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5248728).length < 2 ^ (prefixWord ++ tailWord_5248728).sum := by decide
  have hdescent : baseEnd_5248728 < baseStart_5248728 := by decide
  rcases family_descends (prefixWord ++ tailWord_5248728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5248735 : List Nat := [1, 1, 2, 3, 2, 2, 2, 2, 3, 2, 3]
def baseStart_5248735 : Nat := 118140960795 + 5248735 * 2 ^ 59
def prefixEnd_5248735 : Nat := 4983230072969 + 3 ^ 40 * 5248735 * 2
def baseEnd_5248735 : Nat := 2695123883076627033874013

theorem tailTrace_5248735 : CollatzResearch.WordTrace tailWord_5248735 prefixEnd_5248735 2695123883076627033874013 := by
  unfold tailWord_5248735
  simp only [CollatzResearch.WordTrace]
  refine ⟨191437092639736982416059659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127624728426491321610706439 191437092639736982416059659)
  ·
    refine ⟨287155638959605473624089489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191437092639736982416059659 287155638959605473624089489)
    ·
      refine ⟨215366729219704105218067117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287155638959605473624089489 215366729219704105218067117)
      ·
        refine ⟨80762523457389039456775169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 215366729219704105218067117 80762523457389039456775169)
        ·
          refine ⟨60571892593041779592581377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80762523457389039456775169 60571892593041779592581377)
          ·
            refine ⟨45428919444781334694436033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60571892593041779592581377 45428919444781334694436033)
            ·
              refine ⟨34071689583586001020827025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45428919444781334694436033 34071689583586001020827025)
              ·
                refine ⟨25553767187689500765620269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34071689583586001020827025 25553767187689500765620269)
                ·
                  refine ⟨9582662695383562787107601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25553767187689500765620269 9582662695383562787107601)
                  ·
                    refine ⟨7186997021537672090330701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9582662695383562787107601 7186997021537672090330701)
                    ·
                      refine ⟨2695123883076627033874013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7186997021537672090330701 2695123883076627033874013)
                      ·
                        rfl

theorem cell23_5248735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 3, 2, 3].length) (baseStart_5248735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5248735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5248735 prefixEnd_5248735 := by exact prefixLift 5248735
  have htrace : WordTrace (prefixWord ++ tailWord_5248735) baseStart_5248735 baseEnd_5248735 := by
    simpa [prefixWord, tailWord_5248735, baseEnd_5248735] using wordTrace_append hprefix tailTrace_5248735
  have hstable : (prefixWord ++ tailWord_5248735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5248735).length < 2 ^ (prefixWord ++ tailWord_5248735).sum := by decide
  have hdescent : baseEnd_5248735 < baseStart_5248735 := by decide
  rcases family_descends (prefixWord ++ tailWord_5248735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5248749 : List Nat := [1, 5, 1, 2, 1, 4, 1, 2, 1, 1, 4]
def baseStart_5248749 : Nat := 118140960795 + 5248749 * 2 ^ 59
def prefixEnd_5248749 : Nat := 4983230072969 + 3 ^ 40 * 5248749 * 2
def baseEnd_5248749 : Nat := 2695131071805789979098949

theorem tailTrace_5248749 : CollatzResearch.WordTrace tailWord_5248749 prefixEnd_5248749 2695131071805789979098949 := by
  unfold tailWord_5248749
  simp only [CollatzResearch.WordTrace]
  refine ⟨191437603261686262807069301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127625068841124175204712867 191437603261686262807069301)
  ·
    refine ⟨17947275305783087138162747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 191437603261686262807069301 17947275305783087138162747)
    ·
      refine ⟨26920912958674630707244121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17947275305783087138162747 26920912958674630707244121)
      ·
        refine ⟨20190684719005973030433091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26920912958674630707244121 20190684719005973030433091)
        ·
          refine ⟨30286027078508959545649637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20190684719005973030433091 30286027078508959545649637)
          ·
            refine ⟨5678630077220429914809307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30286027078508959545649637 5678630077220429914809307)
            ·
              refine ⟨8517945115830644872213961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5678630077220429914809307 8517945115830644872213961)
              ·
                refine ⟨6388458836872983654160471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8517945115830644872213961 6388458836872983654160471)
                ·
                  refine ⟨9582688255309475481240707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6388458836872983654160471 9582688255309475481240707)
                  ·
                    refine ⟨14374032382964213221861061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9582688255309475481240707 14374032382964213221861061)
                    ·
                      refine ⟨2695131071805789979098949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14374032382964213221861061 2695131071805789979098949)
                      ·
                        rfl

theorem cell23_5248749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_5248749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5248749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5248749 prefixEnd_5248749 := by exact prefixLift 5248749
  have htrace : WordTrace (prefixWord ++ tailWord_5248749) baseStart_5248749 baseEnd_5248749 := by
    simpa [prefixWord, tailWord_5248749, baseEnd_5248749] using wordTrace_append hprefix tailTrace_5248749
  have hstable : (prefixWord ++ tailWord_5248749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5248749).length < 2 ^ (prefixWord ++ tailWord_5248749).sum := by decide
  have hdescent : baseEnd_5248749 < baseStart_5248749 := by decide
  rcases family_descends (prefixWord ++ tailWord_5248749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5248766 : List Nat := [4, 2, 2, 1, 3, 1, 3, 1, 1, 1, 4]
def baseStart_5248766 : Nat := 118140960795 + 5248766 * 2 ^ 59
def prefixEnd_5248766 : Nat := 4983230072969 + 3 ^ 40 * 5248766 * 2
def baseEnd_5248766 : Nat := 2695139800976916412586371

theorem tailTrace_5248766 : CollatzResearch.WordTrace tailWord_5248766 prefixEnd_5248766 2695139800976916412586371 := by
  unfold tailWord_5248766
  simp only [CollatzResearch.WordTrace]
  refine ⟨23929777912828084338804769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127625482201749783140292101 23929777912828084338804769)
  ·
    refine ⟨17947333434621063254103577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23929777912828084338804769 17947333434621063254103577)
    ·
      refine ⟨13460500075965797440577683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17947333434621063254103577 13460500075965797440577683)
      ·
        refine ⟨20190750113948696160866525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13460500075965797440577683 20190750113948696160866525)
        ·
          refine ⟨7571531292730761060324947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20190750113948696160866525 7571531292730761060324947)
          ·
            refine ⟨11357296939096141590487421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7571531292730761060324947 11357296939096141590487421)
            ·
              refine ⟨4258986352161053096432783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11357296939096141590487421 4258986352161053096432783)
              ·
                refine ⟨6388479528241579644649175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4258986352161053096432783 6388479528241579644649175)
                ·
                  refine ⟨9582719292362369466973763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6388479528241579644649175 9582719292362369466973763)
                  ·
                    refine ⟨14374078938543554200460645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9582719292362369466973763 14374078938543554200460645)
                    ·
                      refine ⟨2695139800976916412586371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14374078938543554200460645 2695139800976916412586371)
                      ·
                        rfl

theorem cell23_5248766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_5248766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5248766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5248766 prefixEnd_5248766 := by exact prefixLift 5248766
  have htrace : WordTrace (prefixWord ++ tailWord_5248766) baseStart_5248766 baseEnd_5248766 := by
    simpa [prefixWord, tailWord_5248766, baseEnd_5248766] using wordTrace_append hprefix tailTrace_5248766
  have hstable : (prefixWord ++ tailWord_5248766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5248766).length < 2 ^ (prefixWord ++ tailWord_5248766).sum := by decide
  have hdescent : baseEnd_5248766 < baseStart_5248766 := by decide
  rcases family_descends (prefixWord ++ tailWord_5248766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5248782 : List Nat := [4, 1, 1, 2, 1, 1, 2, 3, 4, 1, 3]
def baseStart_5248782 : Nat := 118140960795 + 5248782 * 2 ^ 59
def prefixEnd_5248782 : Nat := 4983230072969 + 3 ^ 40 * 5248782 * 2
def baseEnd_5248782 : Nat := 2695148016667388349986297

theorem tailTrace_5248782 : CollatzResearch.WordTrace tailWord_5248782 prefixEnd_5248782 2695148016667388349986297 := by
  unfold tailWord_5248782
  simp only [CollatzResearch.WordTrace]
  refine ⟨23929850858820838680377575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127625871247044472962013733 23929850858820838680377575)
  ·
    refine ⟨35894776288231258020566363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23929850858820838680377575 35894776288231258020566363)
    ·
      refine ⟨53842164432346887030849545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35894776288231258020566363 53842164432346887030849545)
      ·
        refine ⟨40381623324260165273137159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53842164432346887030849545 40381623324260165273137159)
        ·
          refine ⟨60572434986390247909705739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40381623324260165273137159 60572434986390247909705739)
          ·
            refine ⟨90858652479585371864558609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60572434986390247909705739 90858652479585371864558609)
            ·
              refine ⟨68143989359689028898418957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90858652479585371864558609 68143989359689028898418957)
              ·
                refine ⟨25553996009883385836907109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68143989359689028898418957 25553996009883385836907109)
                ·
                  refine ⟨4791374251853134844420083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25553996009883385836907109 4791374251853134844420083)
                  ·
                    refine ⟨7187061377779702266630125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4791374251853134844420083 7187061377779702266630125)
                    ·
                      refine ⟨2695148016667388349986297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7187061377779702266630125 2695148016667388349986297)
                      ·
                        rfl

theorem cell23_5248782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 4, 1, 3].length) (baseStart_5248782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5248782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5248782 prefixEnd_5248782 := by exact prefixLift 5248782
  have htrace : WordTrace (prefixWord ++ tailWord_5248782) baseStart_5248782 baseEnd_5248782 := by
    simpa [prefixWord, tailWord_5248782, baseEnd_5248782] using wordTrace_append hprefix tailTrace_5248782
  have hstable : (prefixWord ++ tailWord_5248782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5248782).length < 2 ^ (prefixWord ++ tailWord_5248782).sum := by decide
  have hdescent : baseEnd_5248782 < baseStart_5248782 := by decide
  rcases family_descends (prefixWord ++ tailWord_5248782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5248792 : List Nat := [2, 1, 2, 3, 1, 1, 3, 2, 3, 3, 2]
def baseStart_5248792 : Nat := 118140960795 + 5248792 * 2 ^ 59
def prefixEnd_5248792 : Nat := 4983230072969 + 3 ^ 40 * 5248792 * 2
def baseEnd_5248792 : Nat := 2695153151473933310861251

theorem tailTrace_5248792 : CollatzResearch.WordTrace tailWord_5248792 prefixEnd_5248792 2695153151473933310861251 := by
  unfold tailWord_5248792
  simp only [CollatzResearch.WordTrace]
  refine ⟨95719585800265240575442315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127626114400353654100589753 95719585800265240575442315)
  ·
    refine ⟨143579378700397860863163473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95719585800265240575442315 143579378700397860863163473)
    ·
      refine ⟨107684534025298395647372605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143579378700397860863163473 107684534025298395647372605)
      ·
        refine ⟨40381700259486898367764727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107684534025298395647372605 40381700259486898367764727)
        ·
          refine ⟨60572550389230347551647091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40381700259486898367764727 60572550389230347551647091)
          ·
            refine ⟨90858825583845521327470637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60572550389230347551647091 90858825583845521327470637)
            ·
              refine ⟨34072059593942070497801489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90858825583845521327470637 34072059593942070497801489)
              ·
                refine ⟨25554044695456552873351117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34072059593942070497801489 25554044695456552873351117)
                ·
                  refine ⟨9582766760796207327506669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25554044695456552873351117 9582766760796207327506669)
                  ·
                    refine ⟨3593537535298577747815001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9582766760796207327506669 3593537535298577747815001)
                    ·
                      refine ⟨2695153151473933310861251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3593537535298577747815001 2695153151473933310861251)
                      ·
                        rfl

theorem cell23_5248792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 3, 3, 2].length) (baseStart_5248792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5248792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5248792 prefixEnd_5248792 := by exact prefixLift 5248792
  have htrace : WordTrace (prefixWord ++ tailWord_5248792) baseStart_5248792 baseEnd_5248792 := by
    simpa [prefixWord, tailWord_5248792, baseEnd_5248792] using wordTrace_append hprefix tailTrace_5248792
  have hstable : (prefixWord ++ tailWord_5248792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5248792).length < 2 ^ (prefixWord ++ tailWord_5248792).sum := by decide
  have hdescent : baseEnd_5248792 < baseStart_5248792 := by decide
  rcases family_descends (prefixWord ++ tailWord_5248792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5248826 : List Nat := [3, 1, 1, 1, 5, 1, 4, 1, 1, 3, 2]
def baseStart_5248826 : Nat := 118140960795 + 5248826 * 2 ^ 59
def prefixEnd_5248826 : Nat := 4983230072969 + 3 ^ 40 * 5248826 * 2
def baseEnd_5248826 : Nat := 2695170609816186177836095

theorem tailTrace_5248826 : CollatzResearch.WordTrace tailWord_5248826 prefixEnd_5248826 2695170609816186177836095 := by
  unfold tailWord_5248826
  simp only [CollatzResearch.WordTrace]
  refine ⟨47860102920601826239405583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127626941121604869971748221 47860102920601826239405583)
  ·
    refine ⟨71790154380902739359108375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47860102920601826239405583 71790154380902739359108375)
    ·
      refine ⟨107685231571354109038662563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71790154380902739359108375 107685231571354109038662563)
      ·
        refine ⟨161527847357031163557993845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107685231571354109038662563 161527847357031163557993845)
        ·
          refine ⟨15143235689721671583561923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 161527847357031163557993845 15143235689721671583561923)
          ·
            refine ⟨22714853534582507375342885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15143235689721671583561923 22714853534582507375342885)
            ·
              refine ⟨4259035037734220132876791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22714853534582507375342885 4259035037734220132876791)
              ·
                refine ⟨6388552556601330199315187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4259035037734220132876791 6388552556601330199315187)
                ·
                  refine ⟨9582828834901995298972781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6388552556601330199315187 9582828834901995298972781)
                  ·
                    refine ⟨3593560813088248237114793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9582828834901995298972781 3593560813088248237114793)
                    ·
                      refine ⟨2695170609816186177836095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3593560813088248237114793 2695170609816186177836095)
                      ·
                        rfl

theorem cell23_5248826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 4, 1, 1, 3, 2].length) (baseStart_5248826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5248826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5248826 prefixEnd_5248826 := by exact prefixLift 5248826
  have htrace : WordTrace (prefixWord ++ tailWord_5248826) baseStart_5248826 baseEnd_5248826 := by
    simpa [prefixWord, tailWord_5248826, baseEnd_5248826] using wordTrace_append hprefix tailTrace_5248826
  have hstable : (prefixWord ++ tailWord_5248826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5248826).length < 2 ^ (prefixWord ++ tailWord_5248826).sum := by decide
  have hdescent : baseEnd_5248826 < baseStart_5248826 := by decide
  rcases family_descends (prefixWord ++ tailWord_5248826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5248835 : List Nat := [1, 1, 1, 3, 1, 5, 1, 2, 2, 2, 4]
def baseStart_5248835 : Nat := 118140960795 + 5248835 * 2 ^ 59
def prefixEnd_5248835 : Nat := 4983230072969 + 3 ^ 40 * 5248835 * 2
def baseEnd_5248835 : Nat := 2695175231142076642623553

theorem tailTrace_5248835 : CollatzResearch.WordTrace tailWord_5248835 prefixEnd_5248835 2695175231142076642623553 := by
  unfold tailWord_5248835
  simp only [CollatzResearch.WordTrace]
  refine ⟨191440739939374699494699959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127627159959583132996466639 191440739939374699494699959)
  ·
    refine ⟨287161109909062049242049939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191440739939374699494699959 287161109909062049242049939)
    ·
      refine ⟨430741664863593073863074909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287161109909062049242049939 430741664863593073863074909)
      ·
        refine ⟨161528124323847402698653091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 430741664863593073863074909 161528124323847402698653091)
        ·
          refine ⟨242292186485771104047979637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161528124323847402698653091 242292186485771104047979637)
          ·
            refine ⟨22714892483041041004498091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 242292186485771104047979637 22714892483041041004498091)
            ·
              refine ⟨34072338724561561506747137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22714892483041041004498091 34072338724561561506747137)
              ·
                refine ⟨25554254043421171130060353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34072338724561561506747137 25554254043421171130060353)
                ·
                  refine ⟨19165690532565878347545265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25554254043421171130060353 19165690532565878347545265)
                  ·
                    refine ⟨14374267899424408760658949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19165690532565878347545265 14374267899424408760658949)
                    ·
                      refine ⟨2695175231142076642623553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14374267899424408760658949 2695175231142076642623553)
                      ·
                        rfl

theorem cell23_5248835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 2, 2, 4].length) (baseStart_5248835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5248835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5248835 prefixEnd_5248835 := by exact prefixLift 5248835
  have htrace : WordTrace (prefixWord ++ tailWord_5248835) baseStart_5248835 baseEnd_5248835 := by
    simpa [prefixWord, tailWord_5248835, baseEnd_5248835] using wordTrace_append hprefix tailTrace_5248835
  have hstable : (prefixWord ++ tailWord_5248835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5248835).length < 2 ^ (prefixWord ++ tailWord_5248835).sum := by decide
  have hdescent : baseEnd_5248835 < baseStart_5248835 := by decide
  rcases family_descends (prefixWord ++ tailWord_5248835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5248852 : List Nat := [2, 4, 1, 1, 3, 1, 2, 1, 2, 2, 4]
def baseStart_5248852 : Nat := 118140960795 + 5248852 * 2 ^ 59
def prefixEnd_5248852 : Nat := 4983230072969 + 3 ^ 40 * 5248852 * 2
def baseEnd_5248852 : Nat := 2695183960313203076110975

theorem tailTrace_5248852 : CollatzResearch.WordTrace tailWord_5248852 prefixEnd_5248852 2695183960313203076110975 := by
  unfold tailWord_5248852
  simp only [CollatzResearch.WordTrace]
  refine ⟨95720679990156555699034405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127627573320208740932045873 95720679990156555699034405)
  ·
    refine ⟨17947627498154354193568951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95720679990156555699034405 17947627498154354193568951)
    ·
      refine ⟨26921441247231531290353427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17947627498154354193568951 26921441247231531290353427)
      ·
        refine ⟨40382161870847296935530141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26921441247231531290353427 40382161870847296935530141)
        ·
          refine ⟨15143310701567736350823803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40382161870847296935530141 15143310701567736350823803)
          ·
            refine ⟨22714966052351604526235705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15143310701567736350823803 22714966052351604526235705)
            ·
              refine ⟨17036224539263703394676779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22714966052351604526235705 17036224539263703394676779)
              ·
                refine ⟨25554336808895555092015169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17036224539263703394676779 25554336808895555092015169)
                ·
                  refine ⟨19165752606671666319011377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25554336808895555092015169 19165752606671666319011377)
                  ·
                    refine ⟨14374314455003749739258533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19165752606671666319011377 14374314455003749739258533)
                    ·
                      refine ⟨2695183960313203076110975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14374314455003749739258533 2695183960313203076110975)
                      ·
                        rfl

theorem cell23_5248852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_5248852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5248852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5248852 prefixEnd_5248852 := by exact prefixLift 5248852
  have htrace : WordTrace (prefixWord ++ tailWord_5248852) baseStart_5248852 baseEnd_5248852 := by
    simpa [prefixWord, tailWord_5248852, baseEnd_5248852] using wordTrace_append hprefix tailTrace_5248852
  have hstable : (prefixWord ++ tailWord_5248852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5248852).length < 2 ^ (prefixWord ++ tailWord_5248852).sum := by decide
  have hdescent : baseEnd_5248852 < baseStart_5248852 := by decide
  rcases family_descends (prefixWord ++ tailWord_5248852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5248875 : List Nat := [1, 1, 1, 1, 2, 2, 3, 5, 2, 5]
def baseStart_5248875 : Nat := 118140960795 + 5248875 * 2 ^ 59
def prefixEnd_5248875 : Nat := 4983230072969 + 3 ^ 40 * 5248875 * 2
def baseEnd_5248875 : Nat := 898398590122752162041123

theorem tailTrace_5248875 : CollatzResearch.WordTrace tailWord_5248875 prefixEnd_5248875 898398590122752162041123 := by
  unfold tailWord_5248875
  simp only [CollatzResearch.WordTrace]
  refine ⟨191442198859229786326156079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127628132572819857550770719 191442198859229786326156079)
  ·
    refine ⟨287163298288844679489234119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191442198859229786326156079 287163298288844679489234119)
    ·
      refine ⟨430744947433267019233851179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287163298288844679489234119 430744947433267019233851179)
      ·
        refine ⟨646117421149900528850776769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 430744947433267019233851179 646117421149900528850776769)
        ·
          refine ⟨484588065862425396638082577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 646117421149900528850776769 484588065862425396638082577)
          ·
            refine ⟨363441049396819047478561933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 484588065862425396638082577 363441049396819047478561933)
            ·
              refine ⟨136290393523807142804460725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 363441049396819047478561933 136290393523807142804460725)
              ·
                refine ⟨12777224392856919637918193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 136290393523807142804460725 12777224392856919637918193)
                ·
                  refine ⟨9582918294642689728438645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12777224392856919637918193 9582918294642689728438645)
                  ·
                    refine ⟨898398590122752162041123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9582918294642689728438645 898398590122752162041123)
                    ·
                      rfl

theorem cell23_5248875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5, 2, 5].length) (baseStart_5248875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5248875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5248875 prefixEnd_5248875 := by exact prefixLift 5248875
  have htrace : WordTrace (prefixWord ++ tailWord_5248875) baseStart_5248875 baseEnd_5248875 := by
    simpa [prefixWord, tailWord_5248875, baseEnd_5248875] using wordTrace_append hprefix tailTrace_5248875
  have hstable : (prefixWord ++ tailWord_5248875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5248875).length < 2 ^ (prefixWord ++ tailWord_5248875).sum := by decide
  have hdescent : baseEnd_5248875 < baseStart_5248875 := by decide
  rcases family_descends (prefixWord ++ tailWord_5248875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5248882 : List Nat := [3, 2, 1, 2, 1, 1, 1, 2, 1, 7, 2]
def baseStart_5248882 : Nat := 118140960795 + 5248882 * 2 ^ 59
def prefixEnd_5248882 : Nat := 4983230072969 + 3 ^ 40 * 5248882 * 2
def baseEnd_5248882 : Nat := 2695199364732837958735837

theorem tailTrace_5248882 : CollatzResearch.WordTrace tailWord_5248882 prefixEnd_5248882 2695199364732837958735837 := by
  unfold tailWord_5248882
  simp only [CollatzResearch.WordTrace]
  refine ⟨47860613542551106630415225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127628302780136284347773933 47860613542551106630415225)
  ·
    refine ⟨35895460156913329972811419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47860613542551106630415225 35895460156913329972811419)
    ·
      refine ⟨53843190235369994959217129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35895460156913329972811419 53843190235369994959217129)
      ·
        refine ⟨40382392676527496219412847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53843190235369994959217129 40382392676527496219412847)
        ·
          refine ⟨60573589014791244329119271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40382392676527496219412847 60573589014791244329119271)
          ·
            refine ⟨90860383522186866493678907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60573589014791244329119271 90860383522186866493678907)
            ·
              refine ⟨136290575283280299740518361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90860383522186866493678907 136290575283280299740518361)
              ·
                refine ⟨102217931462460224805388771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136290575283280299740518361 102217931462460224805388771)
                ·
                  refine ⟨153326897193690337208083157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102217931462460224805388771 153326897193690337208083157)
                  ·
                    refine ⟨3593599152977117278314449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 153326897193690337208083157 3593599152977117278314449)
                    ·
                      refine ⟨2695199364732837958735837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3593599152977117278314449 2695199364732837958735837)
                      ·
                        rfl

theorem cell23_5248882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 1, 7, 2].length) (baseStart_5248882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5248882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5248882 prefixEnd_5248882 := by exact prefixLift 5248882
  have htrace : WordTrace (prefixWord ++ tailWord_5248882) baseStart_5248882 baseEnd_5248882 := by
    simpa [prefixWord, tailWord_5248882, baseEnd_5248882] using wordTrace_append hprefix tailTrace_5248882
  have hstable : (prefixWord ++ tailWord_5248882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5248882).length < 2 ^ (prefixWord ++ tailWord_5248882).sum := by decide
  have hdescent : baseEnd_5248882 < baseStart_5248882 := by decide
  rcases family_descends (prefixWord ++ tailWord_5248882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5248949 : List Nat := [1, 3, 3, 2, 1, 2, 2, 2, 2, 2, 3]
def baseStart_5248949 : Nat := 118140960795 + 5248949 * 2 ^ 59
def prefixEnd_5248949 : Nat := 4983230072969 + 3 ^ 40 * 5248949 * 2
def baseEnd_5248949 : Nat := 2695233767936689196598029

theorem tailTrace_5248949 : CollatzResearch.WordTrace tailWord_5248949 prefixEnd_5248949 2695233767936689196598029 := by
  unfold tailWord_5248949
  simp only [CollatzResearch.WordTrace]
  refine ⟨191444897860961696964349901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127629931907307797976233267 191444897860961696964349901)
  ·
    refine ⟨71791836697860636361631213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191444897860961696964349901 71791836697860636361631213)
    ·
      refine ⟨26921938761697738635611705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71791836697860636361631213 26921938761697738635611705)
      ·
        refine ⟨20191454071273303976708779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26921938761697738635611705 20191454071273303976708779)
        ·
          refine ⟨30287181106909955965063169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20191454071273303976708779 30287181106909955965063169)
          ·
            refine ⟨22715385830182466973797377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30287181106909955965063169 22715385830182466973797377)
            ·
              refine ⟨17036539372636850230348033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22715385830182466973797377 17036539372636850230348033)
              ·
                refine ⟨12777404529477637672761025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17036539372636850230348033 12777404529477637672761025)
                ·
                  refine ⟨9583053397108228254570769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12777404529477637672761025 9583053397108228254570769)
                  ·
                    refine ⟨7187290047831171190928077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9583053397108228254570769 7187290047831171190928077)
                    ·
                      refine ⟨2695233767936689196598029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7187290047831171190928077 2695233767936689196598029)
                      ·
                        rfl

theorem cell23_5248949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_5248949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5248949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5248949 prefixEnd_5248949 := by exact prefixLift 5248949
  have htrace : WordTrace (prefixWord ++ tailWord_5248949) baseStart_5248949 baseEnd_5248949 := by
    simpa [prefixWord, tailWord_5248949, baseEnd_5248949] using wordTrace_append hprefix tailTrace_5248949
  have hstable : (prefixWord ++ tailWord_5248949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5248949).length < 2 ^ (prefixWord ++ tailWord_5248949).sum := by decide
  have hdescent : baseEnd_5248949 < baseStart_5248949 := by decide
  rcases family_descends (prefixWord ++ tailWord_5248949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5248952 : List Nat := [2, 1, 2, 1, 2, 3, 4, 2, 6]
def baseStart_5248952 : Nat := 118140960795 + 5248952 * 2 ^ 59
def prefixEnd_5248952 : Nat := 4983230072969 + 3 ^ 40 * 5248952 * 2
def baseEnd_5248952 : Nat := 299470589819850298317835

theorem tailTrace_5248952 : CollatzResearch.WordTrace tailWord_5248952 prefixEnd_5248952 299470589819850298317835 := by
  unfold tailWord_5248952
  simp only [CollatzResearch.WordTrace]
  refine ⟨95722503639975414238354555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127630004853300552317806073 95722503639975414238354555)
  ·
    refine ⟨143583755459963121357531833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95722503639975414238354555 143583755459963121357531833)
    ·
      refine ⟨107687816594972341018148875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143583755459963121357531833 107687816594972341018148875)
      ·
        refine ⟨161531724892458511527223313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107687816594972341018148875 161531724892458511527223313)
        ·
          refine ⟨121148793669343883645417485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161531724892458511527223313 121148793669343883645417485)
          ·
            refine ⟨45430797626003956367031557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121148793669343883645417485 45430797626003956367031557)
            ·
              refine ⟨8518274554875741818818417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45430797626003956367031557 8518274554875741818818417)
              ·
                refine ⟨6388705916156806364113813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8518274554875741818818417 6388705916156806364113813)
                ·
                  refine ⟨299470589819850298317835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6388705916156806364113813 299470589819850298317835)
                  ·
                    rfl

theorem cell23_5248952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 2, 6].length) (baseStart_5248952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5248952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5248952 prefixEnd_5248952 := by exact prefixLift 5248952
  have htrace : WordTrace (prefixWord ++ tailWord_5248952) baseStart_5248952 baseEnd_5248952 := by
    simpa [prefixWord, tailWord_5248952, baseEnd_5248952] using wordTrace_append hprefix tailTrace_5248952
  have hstable : (prefixWord ++ tailWord_5248952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5248952).length < 2 ^ (prefixWord ++ tailWord_5248952).sum := by decide
  have hdescent : baseEnd_5248952 < baseStart_5248952 := by decide
  rcases family_descends (prefixWord ++ tailWord_5248952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5248975 : List Nat := [1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 7]
def baseStart_5248975 : Nat := 118140960795 + 5248975 * 2 ^ 59
def prefixEnd_5248975 : Nat := 4983230072969 + 3 ^ 40 * 5248975 * 2
def baseEnd_5248975 : Nat := 2695247118433706094872909

theorem tailTrace_5248975 : CollatzResearch.WordTrace tailWord_5248975 prefixEnd_5248975 2695247118433706094872909 := by
  unfold tailWord_5248975
  simp only [CollatzResearch.WordTrace]
  refine ⟨191445846158867503404796379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127630564105911668936530919 191445846158867503404796379)
  ·
    refine ⟨287168769238301255107194569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191445846158867503404796379 287168769238301255107194569)
    ·
      refine ⟨215376576928725941330395927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287168769238301255107194569 215376576928725941330395927)
      ·
        refine ⟨323064865393088911995593891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215376576928725941330395927 323064865393088911995593891)
        ·
          refine ⟨484597298089633367993390837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323064865393088911995593891 484597298089633367993390837)
          ·
            refine ⟨45430996695903128249380391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 484597298089633367993390837 45430996695903128249380391)
            ·
              refine ⟨68146495043854692374070587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45430996695903128249380391 68146495043854692374070587)
              ·
                refine ⟨102219742565782038561105881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68146495043854692374070587 102219742565782038561105881)
                ·
                  refine ⟨76664806924336528920829411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102219742565782038561105881 76664806924336528920829411)
                  ·
                    refine ⟨114997210386504793381244117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 76664806924336528920829411 114997210386504793381244117)
                    ·
                      refine ⟨2695247118433706094872909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 114997210386504793381244117 2695247118433706094872909)
                      ·
                        rfl

theorem cell23_5248975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 7].length) (baseStart_5248975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5248975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5248975 prefixEnd_5248975 := by exact prefixLift 5248975
  have htrace : WordTrace (prefixWord ++ tailWord_5248975) baseStart_5248975 baseEnd_5248975 := by
    simpa [prefixWord, tailWord_5248975, baseEnd_5248975] using wordTrace_append hprefix tailTrace_5248975
  have hstable : (prefixWord ++ tailWord_5248975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5248975).length < 2 ^ (prefixWord ++ tailWord_5248975).sum := by decide
  have hdescent : baseEnd_5248975 < baseStart_5248975 := by decide
  rcases family_descends (prefixWord ++ tailWord_5248975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5249029 : List Nat := [1, 3, 1, 1, 2, 6, 1, 1, 1, 6]
def baseStart_5249029 : Nat := 118140960795 + 5249029 * 2 ^ 59
def prefixEnd_5249029 : Nat := 4983230072969 + 3 ^ 40 * 5249029 * 2
def baseEnd_5249029 : Nat := 898424948796349627865887

theorem tailTrace_5249029 : CollatzResearch.WordTrace tailWord_5249029 prefixEnd_5249029 898424948796349627865887 := by
  unfold tailWord_5249029
  simp only [CollatzResearch.WordTrace]
  refine ⟨191447815700671870627262141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127631877133781247084841427 191447815700671870627262141)
  ·
    refine ⟨71792930887751951485223303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191447815700671870627262141 71792930887751951485223303)
    ·
      refine ⟨107689396331627927227834955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71792930887751951485223303 107689396331627927227834955)
      ·
        refine ⟨161534094497441890841752433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107689396331627927227834955 161534094497441890841752433)
        ·
          refine ⟨121150570873081418131314325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161534094497441890841752433 121150570873081418131314325)
          ·
            refine ⟨5678933009675691474905359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 121150570873081418131314325 5678933009675691474905359)
            ·
              refine ⟨8518399514513537212358039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5678933009675691474905359 8518399514513537212358039)
              ·
                refine ⟨12777599271770305818537059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8518399514513537212358039 12777599271770305818537059)
                ·
                  refine ⟨19166398907655458727805589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12777599271770305818537059 19166398907655458727805589)
                  ·
                    refine ⟨898424948796349627865887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19166398907655458727805589 898424948796349627865887)
                    ·
                      rfl

theorem cell23_5249029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 1, 1, 6].length) (baseStart_5249029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5249029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5249029 prefixEnd_5249029 := by exact prefixLift 5249029
  have htrace : WordTrace (prefixWord ++ tailWord_5249029) baseStart_5249029 baseEnd_5249029 := by
    simpa [prefixWord, tailWord_5249029, baseEnd_5249029] using wordTrace_append hprefix tailTrace_5249029
  have hstable : (prefixWord ++ tailWord_5249029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5249029).length < 2 ^ (prefixWord ++ tailWord_5249029).sum := by decide
  have hdescent : baseEnd_5249029 < baseStart_5249029 := by decide
  rcases family_descends (prefixWord ++ tailWord_5249029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5249032 : List Nat := [2, 1, 3, 2, 1, 2, 3, 1, 1, 1, 6]
def baseStart_5249032 : Nat := 118140960795 + 5249032 * 2 ^ 59
def prefixEnd_5249032 : Nat := 4983230072969 + 3 ^ 40 * 5249032 * 2
def baseEnd_5249032 : Nat := 2695276386831012371860147

theorem tailTrace_5249032 : CollatzResearch.WordTrace tailWord_5249032 prefixEnd_5249032 2695276386831012371860147 := by
  unfold tailWord_5249032
  simp only [CollatzResearch.WordTrace]
  refine ⟨95723962559830501069810675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127631950079774001426414233 95723962559830501069810675)
  ·
    refine ⟨143585943839745751604716013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95723962559830501069810675 143585943839745751604716013)
    ·
      refine ⟨53844728939904656851768505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143585943839745751604716013 53844728939904656851768505)
      ·
        refine ⟨40383546704928492638826379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53844728939904656851768505 40383546704928492638826379)
        ·
          refine ⟨60575320057392738958239569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40383546704928492638826379 60575320057392738958239569)
          ·
            refine ⟨45431490043044554218679677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60575320057392738958239569 45431490043044554218679677)
            ·
              refine ⟨17036808766141707832004879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45431490043044554218679677 17036808766141707832004879)
              ·
                refine ⟨25555213149212561748007319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17036808766141707832004879 25555213149212561748007319)
                ·
                  refine ⟨38332819723818842622010979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25555213149212561748007319 38332819723818842622010979)
                  ·
                    refine ⟨57499229585728263933016469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38332819723818842622010979 57499229585728263933016469)
                    ·
                      refine ⟨2695276386831012371860147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57499229585728263933016469 2695276386831012371860147)
                      ·
                        rfl

theorem cell23_5249032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_5249032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5249032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5249032 prefixEnd_5249032 := by exact prefixLift 5249032
  have htrace : WordTrace (prefixWord ++ tailWord_5249032) baseStart_5249032 baseEnd_5249032 := by
    simpa [prefixWord, tailWord_5249032, baseEnd_5249032] using wordTrace_append hprefix tailTrace_5249032
  have hstable : (prefixWord ++ tailWord_5249032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5249032).length < 2 ^ (prefixWord ++ tailWord_5249032).sum := by decide
  have hdescent : baseEnd_5249032 < baseStart_5249032 := by decide
  rcases family_descends (prefixWord ++ tailWord_5249032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5249036 : List Nat := [2, 2, 1, 2, 3, 1, 1, 4, 3, 2, 2]
def baseStart_5249036 : Nat := 118140960795 + 5249036 * 2 ^ 59
def prefixEnd_5249036 : Nat := 4983230072969 + 3 ^ 40 * 5249036 * 2
def baseEnd_5249036 : Nat := 2695278440753630356210129

theorem tailTrace_5249036 : CollatzResearch.WordTrace tailWord_5249036 prefixEnd_5249036 2695278440753630356210129 := by
  unfold tailWord_5249036
  simp only [CollatzResearch.WordTrace]
  refine ⟨95724035505823255411383481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127632047341097673881844641 95724035505823255411383481)
  ·
    refine ⟨71793026629367441558537611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95724035505823255411383481 71793026629367441558537611)
    ·
      refine ⟨107689539944051162337806417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71793026629367441558537611 107689539944051162337806417)
      ·
        refine ⟨80767154958038371753354813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107689539944051162337806417 80767154958038371753354813)
        ·
          refine ⟨30287683109264389407508055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80767154958038371753354813 30287683109264389407508055)
          ·
            refine ⟨45431524663896584111262083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30287683109264389407508055 45431524663896584111262083)
            ·
              refine ⟨68147286995844876166893125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45431524663896584111262083 68147286995844876166893125)
              ·
                refine ⟨12777616311720914281292461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68147286995844876166893125 12777616311720914281292461)
                ·
                  refine ⟨4791606116895342855484673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12777616311720914281292461 4791606116895342855484673)
                  ·
                    refine ⟨3593704587671507141613505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4791606116895342855484673 3593704587671507141613505)
                    ·
                      refine ⟨2695278440753630356210129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3593704587671507141613505 2695278440753630356210129)
                      ·
                        rfl

theorem cell23_5249036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 4, 3, 2, 2].length) (baseStart_5249036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5249036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5249036 prefixEnd_5249036 := by exact prefixLift 5249036
  have htrace : WordTrace (prefixWord ++ tailWord_5249036) baseStart_5249036 baseEnd_5249036 := by
    simpa [prefixWord, tailWord_5249036, baseEnd_5249036] using wordTrace_append hprefix tailTrace_5249036
  have hstable : (prefixWord ++ tailWord_5249036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5249036).length < 2 ^ (prefixWord ++ tailWord_5249036).sum := by decide
  have hdescent : baseEnd_5249036 < baseStart_5249036 := by decide
  rcases family_descends (prefixWord ++ tailWord_5249036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5249047 : List Nat := [1, 1, 3, 5, 3, 1, 1, 3, 1, 1, 3]
def baseStart_5249047 : Nat := 118140960795 + 5249047 * 2 ^ 59
def prefixEnd_5249047 : Nat := 4983230072969 + 3 ^ 40 * 5249047 * 2
def baseEnd_5249047 : Nat := 2695284089040829813172579

theorem tailTrace_5249047 : CollatzResearch.WordTrace tailWord_5249047 prefixEnd_5249047 2695284089040829813172579 := by
  unfold tailWord_5249047
  simp only [CollatzResearch.WordTrace]
  refine ⟨191448472214606659701417395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127632314809737773134278263 191448472214606659701417395)
  ·
    refine ⟨287172708321909989552126093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191448472214606659701417395 287172708321909989552126093)
    ·
      refine ⟨107689765620716246082047285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 287172708321909989552126093 107689765620716246082047285)
      ·
        refine ⟨10095915526942148070191933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 107689765620716246082047285 10095915526942148070191933)
        ·
          refine ⟨3785968322603305526321975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10095915526942148070191933 3785968322603305526321975)
          ·
            refine ⟨5678952483904958289482963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3785968322603305526321975 5678952483904958289482963)
            ·
              refine ⟨8518428725857437434224445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5678952483904958289482963 8518428725857437434224445)
              ·
                refine ⟨3194410772196539037834167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8518428725857437434224445 3194410772196539037834167)
                ·
                  refine ⟨4791616158294808556751251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3194410772196539037834167 4791616158294808556751251)
                  ·
                    refine ⟨7187424237442212835126877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4791616158294808556751251 7187424237442212835126877)
                    ·
                      refine ⟨2695284089040829813172579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7187424237442212835126877 2695284089040829813172579)
                      ·
                        rfl

theorem cell23_5249047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_5249047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5249047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5249047 prefixEnd_5249047 := by exact prefixLift 5249047
  have htrace : WordTrace (prefixWord ++ tailWord_5249047) baseStart_5249047 baseEnd_5249047 := by
    simpa [prefixWord, tailWord_5249047, baseEnd_5249047] using wordTrace_append hprefix tailTrace_5249047
  have hstable : (prefixWord ++ tailWord_5249047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5249047).length < 2 ^ (prefixWord ++ tailWord_5249047).sum := by decide
  have hdescent : baseEnd_5249047 < baseStart_5249047 := by decide
  rcases family_descends (prefixWord ++ tailWord_5249047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5249070 : List Nat := [4, 1, 3, 1, 1, 4, 1, 1, 3, 2, 2]
def baseStart_5249070 : Nat := 118140960795 + 5249070 * 2 ^ 59
def prefixEnd_5249070 : Nat := 4983230072969 + 3 ^ 40 * 5249070 * 2
def baseEnd_5249070 : Nat := 2695295899095883223184973

theorem tailTrace_5249070 : CollatzResearch.WordTrace tailWord_5249070 prefixEnd_5249070 2695295899095883223184973 := by
  unfold tailWord_5249070
  simp only [CollatzResearch.WordTrace]
  refine ⟨23931163886690416828688083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127632874062348889753003109 23931163886690416828688083)
  ·
    refine ⟨35896745830035625243032125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23931163886690416828688083 35896745830035625243032125)
    ·
      refine ⟨13461279686263359466137047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35896745830035625243032125 13461279686263359466137047)
      ·
        refine ⟨20191919529395039199205571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13461279686263359466137047 20191919529395039199205571)
        ·
          refine ⟨30287879294092558798808357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20191919529395039199205571 30287879294092558798808357)
          ·
            refine ⟨5678977367642354774776567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30287879294092558798808357 5678977367642354774776567)
            ·
              refine ⟨8518466051463532162164851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5678977367642354774776567 8518466051463532162164851)
              ·
                refine ⟨12777699077195298243247277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8518466051463532162164851 12777699077195298243247277)
                ·
                  refine ⟨4791637153948236841217729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12777699077195298243247277 4791637153948236841217729)
                  ·
                    refine ⟨3593727865461177630913297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4791637153948236841217729 3593727865461177630913297)
                    ·
                      refine ⟨2695295899095883223184973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3593727865461177630913297 2695295899095883223184973)
                      ·
                        rfl

theorem cell23_5249070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_5249070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5249070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5249070 prefixEnd_5249070 := by exact prefixLift 5249070
  have htrace : WordTrace (prefixWord ++ tailWord_5249070) baseStart_5249070 baseEnd_5249070 := by
    simpa [prefixWord, tailWord_5249070, baseEnd_5249070] using wordTrace_append hprefix tailTrace_5249070
  have hstable : (prefixWord ++ tailWord_5249070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5249070).length < 2 ^ (prefixWord ++ tailWord_5249070).sum := by decide
  have hdescent : baseEnd_5249070 < baseStart_5249070 := by decide
  rcases family_descends (prefixWord ++ tailWord_5249070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5249076 : List Nat := [2, 5, 1, 2, 2, 1, 2, 8]
def baseStart_5249076 : Nat := 118140960795 + 5249076 * 2 ^ 59
def prefixEnd_5249076 : Nat := 4983230072969 + 3 ^ 40 * 5249076 * 2
def baseEnd_5249076 : Nat := 99825888147400377767035

theorem tailTrace_5249076 : CollatzResearch.WordTrace tailWord_5249076 prefixEnd_5249076 99825888147400377767035 := by
  unfold tailWord_5249076
  simp only [CollatzResearch.WordTrace]
  refine ⟨95724764965750798827111541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127633019954334398436148721 95724764965750798827111541)
  ·
    refine ⟨8974196715539137390041707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 95724764965750798827111541 8974196715539137390041707)
    ·
      refine ⟨13461295073308706085062561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8974196715539137390041707 13461295073308706085062561)
      ·
        refine ⟨10095971304981529563796921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13461295073308706085062561 10095971304981529563796921)
        ·
          refine ⟨7571978478736147172847691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10095971304981529563796921 7571978478736147172847691)
          ·
            refine ⟨11357967718104220759271537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7571978478736147172847691 11357967718104220759271537)
            ·
              refine ⟨8518475788578165569453653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11357967718104220759271537 8518475788578165569453653)
              ·
                refine ⟨99825888147400377767035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8518475788578165569453653 99825888147400377767035)
                ·
                  rfl

theorem cell23_5249076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 8].length) (baseStart_5249076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5249076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5249076 prefixEnd_5249076 := by exact prefixLift 5249076
  have htrace : WordTrace (prefixWord ++ tailWord_5249076) baseStart_5249076 baseEnd_5249076 := by
    simpa [prefixWord, tailWord_5249076, baseEnd_5249076] using wordTrace_append hprefix tailTrace_5249076
  have hstable : (prefixWord ++ tailWord_5249076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5249076).length < 2 ^ (prefixWord ++ tailWord_5249076).sum := by decide
  have hdescent : baseEnd_5249076 < baseStart_5249076 := by decide
  rcases family_descends (prefixWord ++ tailWord_5249076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5249080 : List Nat := [2, 1, 2, 1, 7, 1, 2, 1, 2, 4]
def baseStart_5249080 : Nat := 118140960795 + 5249080 * 2 ^ 59
def prefixEnd_5249080 : Nat := 4983230072969 + 3 ^ 40 * 5249080 * 2
def baseEnd_5249080 : Nat := 898433677967476061353309

theorem tailTrace_5249080 : CollatzResearch.WordTrace tailWord_5249080 prefixEnd_5249080 898433677967476061353309 := by
  unfold tailWord_5249080
  simp only [CollatzResearch.WordTrace]
  refine ⟨95724837911743553168684347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127633117215658070891579129 95724837911743553168684347)
  ·
    refine ⟨143587256867615329753026521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95724837911743553168684347 143587256867615329753026521)
    ·
      refine ⟨107690442650711497314769891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143587256867615329753026521 107690442650711497314769891)
      ·
        refine ⟨161535663976067245972154837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107690442650711497314769891 161535663976067245972154837)
        ·
          refine ⟨3785992124439076077472379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 161535663976067245972154837 3785992124439076077472379)
          ·
            refine ⟨5678988186658614116208569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3785992124439076077472379 5678988186658614116208569)
            ·
              refine ⟨4259241139993960587156427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5678988186658614116208569 4259241139993960587156427)
              ·
                refine ⟨6388861709990940880734641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4259241139993960587156427 6388861709990940880734641)
                ·
                  refine ⟨4791646282493205660550981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6388861709990940880734641 4791646282493205660550981)
                  ·
                    refine ⟨898433677967476061353309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4791646282493205660550981 898433677967476061353309)
                    ·
                      rfl

theorem cell23_5249080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 2, 1, 2, 4].length) (baseStart_5249080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5249080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5249080 prefixEnd_5249080 := by exact prefixLift 5249080
  have htrace : WordTrace (prefixWord ++ tailWord_5249080) baseStart_5249080 baseEnd_5249080 := by
    simpa [prefixWord, tailWord_5249080, baseEnd_5249080] using wordTrace_append hprefix tailTrace_5249080
  have hstable : (prefixWord ++ tailWord_5249080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5249080).length < 2 ^ (prefixWord ++ tailWord_5249080).sum := by decide
  have hdescent : baseEnd_5249080 < baseStart_5249080 := by decide
  rcases family_descends (prefixWord ++ tailWord_5249080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5249096 : List Nat := [2, 1, 3, 1, 1, 1, 2, 6, 1, 3, 2]
def baseStart_5249096 : Nat := 118140960795 + 5249096 * 2 ^ 59
def prefixEnd_5249096 : Nat := 4983230072969 + 3 ^ 40 * 5249096 * 2
def baseEnd_5249096 : Nat := 2695309249592900121459853

theorem tailTrace_5249096 : CollatzResearch.WordTrace tailWord_5249096 prefixEnd_5249096 2695309249592900121459853 := by
  unfold tailWord_5249096
  simp only [CollatzResearch.WordTrace]
  refine ⟨95725129695714570534975571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127633506260952760713300761 95725129695714570534975571)
  ·
    refine ⟨143587694543571855802463357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95725129695714570534975571 143587694543571855802463357)
    ·
      refine ⟨53845385453839445925923759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143587694543571855802463357 53845385453839445925923759)
      ·
        refine ⟨80768078180759168888885639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53845385453839445925923759 80768078180759168888885639)
        ·
          refine ⟨121152117271138753333328459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80768078180759168888885639 121152117271138753333328459)
          ·
            refine ⟨181728175906708129999992689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121152117271138753333328459 181728175906708129999992689)
            ·
              refine ⟨136296131930031097499994517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 181728175906708129999992689 136296131930031097499994517)
              ·
                refine ⟨6388881184220207695312243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 136296131930031097499994517 6388881184220207695312243)
                ·
                  refine ⟨9583321776330311542968365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6388881184220207695312243 9583321776330311542968365)
                  ·
                    refine ⟨3593745666123866828613137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9583321776330311542968365 3593745666123866828613137)
                    ·
                      refine ⟨2695309249592900121459853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3593745666123866828613137 2695309249592900121459853)
                      ·
                        rfl

theorem cell23_5249096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 6, 1, 3, 2].length) (baseStart_5249096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5249096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5249096 prefixEnd_5249096 := by exact prefixLift 5249096
  have htrace : WordTrace (prefixWord ++ tailWord_5249096) baseStart_5249096 baseEnd_5249096 := by
    simpa [prefixWord, tailWord_5249096, baseEnd_5249096] using wordTrace_append hprefix tailTrace_5249096
  have hstable : (prefixWord ++ tailWord_5249096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5249096).length < 2 ^ (prefixWord ++ tailWord_5249096).sum := by decide
  have hdescent : baseEnd_5249096 < baseStart_5249096 := by decide
  rcases family_descends (prefixWord ++ tailWord_5249096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5249113 : List Nat := [1, 2, 1, 2, 2, 1, 7, 1, 1, 3, 2]
def baseStart_5249113 : Nat := 118140960795 + 5249113 * 2 ^ 59
def prefixEnd_5249113 : Nat := 4983230072969 + 3 ^ 40 * 5249113 * 2
def baseEnd_5249113 : Nat := 2695317978764026554947275

theorem tailTrace_5249113 : CollatzResearch.WordTrace tailWord_5249113 prefixEnd_5249113 2695317978764026554947275 := by
  unfold tailWord_5249113
  simp only [CollatzResearch.WordTrace]
  refine ⟨191450879432367552973319993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127633919621578368648879995 191450879432367552973319993)
  ·
    refine ⟨143588159574275664729989995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191450879432367552973319993 143588159574275664729989995)
    ·
      refine ⟨215382239361413497094984993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143588159574275664729989995 215382239361413497094984993)
      ·
        refine ⟨161536679521060122821238745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215382239361413497094984993 161536679521060122821238745)
        ·
          refine ⟨121152509640795092115929059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161536679521060122821238745 121152509640795092115929059)
          ·
            refine ⟨181728764461192638173893589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121152509640795092115929059 181728764461192638173893589)
            ·
              refine ⟨4259267917059202457200631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 181728764461192638173893589 4259267917059202457200631)
              ·
                refine ⟨6388901875588803685800947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4259267917059202457200631 6388901875588803685800947)
                ·
                  refine ⟨9583352813383205528701421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6388901875588803685800947 9583352813383205528701421)
                  ·
                    refine ⟨3593757305018702073263033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9583352813383205528701421 3593757305018702073263033)
                    ·
                      refine ⟨2695317978764026554947275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3593757305018702073263033 2695317978764026554947275)
                      ·
                        rfl

theorem cell23_5249113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7, 1, 1, 3, 2].length) (baseStart_5249113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5249113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5249113 prefixEnd_5249113 := by exact prefixLift 5249113
  have htrace : WordTrace (prefixWord ++ tailWord_5249113) baseStart_5249113 baseEnd_5249113 := by
    simpa [prefixWord, tailWord_5249113, baseEnd_5249113] using wordTrace_append hprefix tailTrace_5249113
  have hstable : (prefixWord ++ tailWord_5249113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5249113).length < 2 ^ (prefixWord ++ tailWord_5249113).sum := by decide
  have hdescent : baseEnd_5249113 < baseStart_5249113 := by decide
  rcases family_descends (prefixWord ++ tailWord_5249113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5249143 : List Nat := [1, 1, 3, 1, 1, 5, 2, 3, 2, 2, 2]
def baseStart_5249143 : Nat := 118140960795 + 5249143 * 2 ^ 59
def prefixEnd_5249143 : Nat := 4983230072969 + 3 ^ 40 * 5249143 * 2
def baseEnd_5249143 : Nat := 2695333383183661437572137

theorem tailTrace_5249143 : CollatzResearch.WordTrace tailWord_5249143 prefixEnd_5249143 2695333383183661437572137 := by
  unfold tailWord_5249143
  simp only [CollatzResearch.WordTrace]
  refine ⟨191451973622258868096912083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127634649081505912064608055 191451973622258868096912083)
  ·
    refine ⟨287177960433388302145368125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191451973622258868096912083 287177960433388302145368125)
    ·
      refine ⟨107691735162520613304513047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 287177960433388302145368125 107691735162520613304513047)
      ·
        refine ⟨161537602743780919956769571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107691735162520613304513047 161537602743780919956769571)
        ·
          refine ⟨242306404115671379935154357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161537602743780919956769571 242306404115671379935154357)
          ·
            refine ⟨22716225385844191868920721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 242306404115671379935154357 22716225385844191868920721)
            ·
              refine ⟨17037169039383143901690541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22716225385844191868920721 17037169039383143901690541)
              ·
                refine ⟨6388938389768678963133953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17037169039383143901690541 6388938389768678963133953)
                ·
                  refine ⟨4791703792326509222350465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6388938389768678963133953 4791703792326509222350465)
                  ·
                    refine ⟨3593777844244881916762849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4791703792326509222350465 3593777844244881916762849)
                    ·
                      refine ⟨2695333383183661437572137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3593777844244881916762849 2695333383183661437572137)
                      ·
                        rfl

theorem cell23_5249143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 3, 2, 2, 2].length) (baseStart_5249143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5249143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5249143 prefixEnd_5249143 := by exact prefixLift 5249143
  have htrace : WordTrace (prefixWord ++ tailWord_5249143) baseStart_5249143 baseEnd_5249143 := by
    simpa [prefixWord, tailWord_5249143, baseEnd_5249143] using wordTrace_append hprefix tailTrace_5249143
  have hstable : (prefixWord ++ tailWord_5249143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5249143).length < 2 ^ (prefixWord ++ tailWord_5249143).sum := by decide
  have hdescent : baseEnd_5249143 < baseStart_5249143 := by decide
  rcases family_descends (prefixWord ++ tailWord_5249143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5249149 : List Nat := [1, 4, 1, 1, 3, 3, 1, 2, 7]
def baseStart_5249149 : Nat := 118140960795 + 5249149 * 2 ^ 59
def prefixEnd_5249149 : Nat := 4983230072969 + 3 ^ 40 * 5249149 * 2
def baseEnd_5249149 : Nat := 299481829340843157121901

theorem tailTrace_5249149 : CollatzResearch.WordTrace tailWord_5249149 prefixEnd_5249149 299481829340843157121901 := by
  unfold tailWord_5249149
  simp only [CollatzResearch.WordTrace]
  refine ⟨191452192460237131121630501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127634794973491420747753667 191452192460237131121630501)
  ·
    refine ⟨35897286086294462085305719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 191452192460237131121630501 35897286086294462085305719)
    ·
      refine ⟨53845929129441693127958579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35897286086294462085305719 53845929129441693127958579)
      ·
        refine ⟨80768893694162539691937869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53845929129441693127958579 80768893694162539691937869)
        ·
          refine ⟨30288335135310952384476701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80768893694162539691937869 30288335135310952384476701)
          ·
            refine ⟨11358125675741607144178763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30288335135310952384476701 11358125675741607144178763)
            ·
              refine ⟨17037188513612410716268145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11358125675741607144178763 17037188513612410716268145)
              ·
                refine ⟨12777891385209308037201109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17037188513612410716268145 12777891385209308037201109)
                ·
                  refine ⟨299481829340843157121901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12777891385209308037201109 299481829340843157121901)
                  ·
                    rfl

theorem cell23_5249149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 2, 7].length) (baseStart_5249149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5249149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5249149 prefixEnd_5249149 := by exact prefixLift 5249149
  have htrace : WordTrace (prefixWord ++ tailWord_5249149) baseStart_5249149 baseEnd_5249149 := by
    simpa [prefixWord, tailWord_5249149, baseEnd_5249149] using wordTrace_append hprefix tailTrace_5249149
  have hstable : (prefixWord ++ tailWord_5249149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5249149).length < 2 ^ (prefixWord ++ tailWord_5249149).sum := by decide
  have hdescent : baseEnd_5249149 < baseStart_5249149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5249149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5249194 : List Nat := [3, 1, 5, 1, 2, 1, 3, 1, 2, 2, 2]
def baseStart_5249194 : Nat := 118140960795 + 5249194 * 2 ^ 59
def prefixEnd_5249194 : Nat := 4983230072969 + 3 ^ 40 * 5249194 * 2
def baseEnd_5249194 : Nat := 2695359570697040738034403

theorem tailTrace_5249194 : CollatzResearch.WordTrace tailWord_5249194 prefixEnd_5249194 2695359570697040738034403 := by
  unfold tailWord_5249194
  simp only [CollatzResearch.WordTrace]
  refine ⟨47863458436268525951754659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127635889163382735871345757 47863458436268525951754659)
  ·
    refine ⟨71795187654402788927631989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47863458436268525951754659 71795187654402788927631989)
    ·
      refine ⟨6730798842600261461965499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 71795187654402788927631989 6730798842600261461965499)
      ·
        refine ⟨10096198263900392192948249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6730798842600261461965499 10096198263900392192948249)
        ·
          refine ⟨7572148697925294144711187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10096198263900392192948249 7572148697925294144711187)
          ·
            refine ⟨11358223046887941217066781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7572148697925294144711187 11358223046887941217066781)
            ·
              refine ⟨4259333642582977956400043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11358223046887941217066781 4259333642582977956400043)
              ·
                refine ⟨6389000463874466934600065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4259333642582977956400043 6389000463874466934600065)
                ·
                  refine ⟨4791750347905850200950049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6389000463874466934600065 4791750347905850200950049)
                  ·
                    refine ⟨3593812760929387650712537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4791750347905850200950049 3593812760929387650712537)
                    ·
                      refine ⟨2695359570697040738034403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3593812760929387650712537 2695359570697040738034403)
                      ·
                        rfl

theorem cell23_5249194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_5249194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5249194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5249194 prefixEnd_5249194 := by exact prefixLift 5249194
  have htrace : WordTrace (prefixWord ++ tailWord_5249194) baseStart_5249194 baseEnd_5249194 := by
    simpa [prefixWord, tailWord_5249194, baseEnd_5249194] using wordTrace_append hprefix tailTrace_5249194
  have hstable : (prefixWord ++ tailWord_5249194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5249194).length < 2 ^ (prefixWord ++ tailWord_5249194).sum := by decide
  have hdescent : baseEnd_5249194 < baseStart_5249194 := by decide
  rcases family_descends (prefixWord ++ tailWord_5249194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5249217 : List Nat := [1, 2, 6, 1, 3, 1, 1, 3, 5]
def baseStart_5249217 : Nat := 118140960795 + 5249217 * 2 ^ 59
def prefixEnd_5249217 : Nat := 4983230072969 + 3 ^ 40 * 5249217 * 2
def baseEnd_5249217 : Nat := 299485708972454905338533

theorem tailTrace_5249217 : CollatzResearch.WordTrace tailWord_5249217 prefixEnd_5249217 299485708972454905338533 := by
  unfold tailWord_5249217
  simp only [CollatzResearch.WordTrace]
  refine ⟨191454672623990778735105905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127636448415993852490070603 191454672623990778735105905)
  ·
    refine ⟨143591004467993084051329429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191454672623990778735105905 143591004467993084051329429)
    ·
      refine ⟨6730828334437175814906067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 143591004467993084051329429 6730828334437175814906067)
      ·
        refine ⟨10096242501655763722359101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6730828334437175814906067 10096242501655763722359101)
        ·
          refine ⟨3786090938120911395884663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10096242501655763722359101 3786090938120911395884663)
          ·
            refine ⟨5679136407181367093826995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3786090938120911395884663 5679136407181367093826995)
            ·
              refine ⟨8518704610772050640740493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5679136407181367093826995 8518704610772050640740493)
              ·
                refine ⟨3194514229039518990277685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8518704610772050640740493 3194514229039518990277685)
                ·
                  refine ⟨299485708972454905338533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3194514229039518990277685 299485708972454905338533)
                  ·
                    rfl

theorem cell23_5249217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 3, 5].length) (baseStart_5249217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5249217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5249217 prefixEnd_5249217 := by exact prefixLift 5249217
  have htrace : WordTrace (prefixWord ++ tailWord_5249217) baseStart_5249217 baseEnd_5249217 := by
    simpa [prefixWord, tailWord_5249217, baseEnd_5249217] using wordTrace_append hprefix tailTrace_5249217
  have hstable : (prefixWord ++ tailWord_5249217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5249217).length < 2 ^ (prefixWord ++ tailWord_5249217).sum := by decide
  have hdescent : baseEnd_5249217 < baseStart_5249217 := by decide
  rcases family_descends (prefixWord ++ tailWord_5249217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5249239 : List Nat := [1, 1, 3, 2, 1, 2, 1, 6, 6]
def baseStart_5249239 : Nat := 118140960795 + 5249239 * 2 ^ 59
def prefixEnd_5249239 : Nat := 4983230072969 + 3 ^ 40 * 5249239 * 2
def baseEnd_5249239 : Nat := 299486964147388117996855

theorem tailTrace_5249239 : CollatzResearch.WordTrace tailWord_5249239 prefixEnd_5249239 299486964147388117996855 := by
  unfold tailWord_5249239
  simp only [CollatzResearch.WordTrace]
  refine ⟨191455475029911076492406771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127636983353274050994937847 191455475029911076492406771)
  ·
    refine ⟨287183212544866614738610157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191455475029911076492406771 287183212544866614738610157)
    ·
      refine ⟨107693704704324980526978809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 287183212544866614738610157 107693704704324980526978809)
      ·
        refine ⟨80770278528243735395234107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107693704704324980526978809 80770278528243735395234107)
        ·
          refine ⟨121155417792365603092851161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80770278528243735395234107 121155417792365603092851161)
          ·
            refine ⟨90866563344274202319638371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121155417792365603092851161 90866563344274202319638371)
            ·
              refine ⟨136299845016411303479457557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90866563344274202319638371 136299845016411303479457557)
              ·
                refine ⟨6389055235144279850599573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 136299845016411303479457557 6389055235144279850599573)
                ·
                  refine ⟨299486964147388117996855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6389055235144279850599573 299486964147388117996855)
                  ·
                    rfl

theorem cell23_5249239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 6, 6].length) (baseStart_5249239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5249239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5249239 prefixEnd_5249239 := by exact prefixLift 5249239
  have htrace : WordTrace (prefixWord ++ tailWord_5249239) baseStart_5249239 baseEnd_5249239 := by
    simpa [prefixWord, tailWord_5249239, baseEnd_5249239] using wordTrace_append hprefix tailTrace_5249239
  have hstable : (prefixWord ++ tailWord_5249239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5249239).length < 2 ^ (prefixWord ++ tailWord_5249239).sum := by decide
  have hdescent : baseEnd_5249239 < baseStart_5249239 := by decide
  rcases family_descends (prefixWord ++ tailWord_5249239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5249256 : List Nat := [2, 1, 4, 1, 2, 3, 1, 3, 6]
def baseStart_5249256 : Nat := 118140960795 + 5249256 * 2 ^ 59
def prefixEnd_5249256 : Nat := 4983230072969 + 3 ^ 40 * 5249256 * 2
def baseEnd_5249256 : Nat := 299487934055291055051013

theorem tailTrace_5249256 : CollatzResearch.WordTrace tailWord_5249256 prefixEnd_5249256 299487934055291055051013 := by
  unfold tailWord_5249256
  simp only [CollatzResearch.WordTrace]
  refine ⟨95728047535424744197887811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127637396713899658930517081 95728047535424744197887811)
  ·
    refine ⟨143592071303137116296831717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95728047535424744197887811 143592071303137116296831717)
    ·
      refine ⟨26923513369338209305655947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 143592071303137116296831717 26923513369338209305655947)
      ·
        refine ⟨40385270054007313958483921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26923513369338209305655947 40385270054007313958483921)
        ·
          refine ⟨30288952540505485468862941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40385270054007313958483921 30288952540505485468862941)
          ·
            refine ⟨11358357202689557050823603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30288952540505485468862941 11358357202689557050823603)
            ·
              refine ⟨17037535804034335576235405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11358357202689557050823603 17037535804034335576235405)
              ·
                refine ⟨6389075926512875841088277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17037535804034335576235405 6389075926512875841088277)
                ·
                  refine ⟨299487934055291055051013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6389075926512875841088277 299487934055291055051013)
                  ·
                    rfl

theorem cell23_5249256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 3, 6].length) (baseStart_5249256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5249256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5249256 prefixEnd_5249256 := by exact prefixLift 5249256
  have htrace : WordTrace (prefixWord ++ tailWord_5249256) baseStart_5249256 baseEnd_5249256 := by
    simpa [prefixWord, tailWord_5249256, baseEnd_5249256] using wordTrace_append hprefix tailTrace_5249256
  have hstable : (prefixWord ++ tailWord_5249256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5249256).length < 2 ^ (prefixWord ++ tailWord_5249256).sum := by decide
  have hdescent : baseEnd_5249256 < baseStart_5249256 := by decide
  rcases family_descends (prefixWord ++ tailWord_5249256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5249316 : List Nat := [2, 3, 1, 3, 1, 2, 1, 3, 1, 6]
def baseStart_5249316 : Nat := 118140960795 + 5249316 * 2 ^ 59
def prefixEnd_5249316 : Nat := 4983230072969 + 3 ^ 40 * 5249316 * 2
def baseEnd_5249316 : Nat := 898474071778963086902947

theorem tailTrace_5249316 : CollatzResearch.WordTrace tailWord_5249316 prefixEnd_5249316 898474071778963086902947 := by
  unfold tailWord_5249316
  simp only [CollatzResearch.WordTrace]
  refine ⟨95729141725316059321479901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127638855633754745761973201 95729141725316059321479901)
  ·
    refine ⟨35898428146993522245554963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95729141725316059321479901 35898428146993522245554963)
    ·
      refine ⟨53847642220490283368332445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35898428146993522245554963 53847642220490283368332445)
      ·
        refine ⟨20192865832683856263124667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53847642220490283368332445 20192865832683856263124667)
        ·
          refine ⟨30289298749025784394687001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20192865832683856263124667 30289298749025784394687001)
          ·
            refine ⟨22716974061769338296015251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30289298749025784394687001 22716974061769338296015251)
            ·
              refine ⟨34075461092654007444022877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22716974061769338296015251 34075461092654007444022877)
              ·
                refine ⟨12778297909745252791508579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34075461092654007444022877 12778297909745252791508579)
                ·
                  refine ⟨19167446864617879187262869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12778297909745252791508579 19167446864617879187262869)
                  ·
                    refine ⟨898474071778963086902947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19167446864617879187262869 898474071778963086902947)
                    ·
                      rfl

theorem cell23_5249316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 3, 1, 6].length) (baseStart_5249316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5249316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5249316 prefixEnd_5249316 := by exact prefixLift 5249316
  have htrace : WordTrace (prefixWord ++ tailWord_5249316) baseStart_5249316 baseEnd_5249316 := by
    simpa [prefixWord, tailWord_5249316, baseEnd_5249316] using wordTrace_append hprefix tailTrace_5249316
  have hstable : (prefixWord ++ tailWord_5249316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5249316).length < 2 ^ (prefixWord ++ tailWord_5249316).sum := by decide
  have hdescent : baseEnd_5249316 < baseStart_5249316 := by decide
  rcases family_descends (prefixWord ++ tailWord_5249316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5249336 : List Nat := [2, 1, 2, 1, 3, 1, 4, 2, 1, 2, 4]
def baseStart_5249336 : Nat := 118140960795 + 5249336 * 2 ^ 59
def prefixEnd_5249336 : Nat := 4983230072969 + 3 ^ 40 * 5249336 * 2
def baseEnd_5249336 : Nat := 2695432484949979182458749

theorem tailTrace_5249336 : CollatzResearch.WordTrace tailWord_5249336 prefixEnd_5249336 2695432484949979182458749 := by
  unfold tailWord_5249336
  simp only [CollatzResearch.WordTrace]
  refine ⟨95729506455279831029343931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127639341940373108039125241 95729506455279831029343931)
  ·
    refine ⟨143594259682919746544015897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95729506455279831029343931 143594259682919746544015897)
    ·
      refine ⟨107695694762189809908011923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143594259682919746544015897 107695694762189809908011923)
      ·
        refine ⟨161543542143284714862017885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107695694762189809908011923 161543542143284714862017885)
        ·
          refine ⟨60578828303731768073256707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161543542143284714862017885 60578828303731768073256707)
          ·
            refine ⟨90868242455597652109885061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60578828303731768073256707 90868242455597652109885061)
            ·
              refine ⟨17037795460424559770603449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90868242455597652109885061 17037795460424559770603449)
              ·
                refine ⟨12778346595318419827952587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17037795460424559770603449 12778346595318419827952587)
                ·
                  refine ⟨19167519892977629741928881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12778346595318419827952587 19167519892977629741928881)
                  ·
                    refine ⟨14375639919733222306446661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19167519892977629741928881 14375639919733222306446661)
                    ·
                      refine ⟨2695432484949979182458749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14375639919733222306446661 2695432484949979182458749)
                      ·
                        rfl

theorem cell23_5249336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 2, 1, 2, 4].length) (baseStart_5249336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5249336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5249336 prefixEnd_5249336 := by exact prefixLift 5249336
  have htrace : WordTrace (prefixWord ++ tailWord_5249336) baseStart_5249336 baseEnd_5249336 := by
    simpa [prefixWord, tailWord_5249336, baseEnd_5249336] using wordTrace_append hprefix tailTrace_5249336
  have hstable : (prefixWord ++ tailWord_5249336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5249336).length < 2 ^ (prefixWord ++ tailWord_5249336).sum := by decide
  have hdescent : baseEnd_5249336 < baseStart_5249336 := by decide
  rcases family_descends (prefixWord ++ tailWord_5249336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5249343 : List Nat := [1, 1, 2, 2, 4, 1, 3, 3, 1, 2, 3]
def baseStart_5249343 : Nat := 118140960795 + 5249343 * 2 ^ 59
def prefixEnd_5249343 : Nat := 4983230072969 + 3 ^ 40 * 5249343 * 2
def baseEnd_5249343 : Nat := 2695436079314560655071217

theorem tailTrace_5249343 : CollatzResearch.WordTrace tailWord_5249343 prefixEnd_5249343 2695436079314560655071217 := by
  unfold tailWord_5249343
  simp only [CollatzResearch.WordTrace]
  refine ⟨191459268221534302254192683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127639512147689534836128455 191459268221534302254192683)
  ·
    refine ⟨287188902332301453381289025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191459268221534302254192683 287188902332301453381289025)
    ·
      refine ⟨215391676749226090035966769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287188902332301453381289025 215391676749226090035966769)
      ·
        refine ⟨161543757561919567526975077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215391676749226090035966769 161543757561919567526975077)
        ·
          refine ⟨30289454542859918911307827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 161543757561919567526975077 30289454542859918911307827)
          ·
            refine ⟨45434181814289878366961741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30289454542859918911307827 45434181814289878366961741)
            ·
              refine ⟨17037818180358704387610653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45434181814289878366961741 17037818180358704387610653)
              ·
                refine ⟨6389181817634514145353995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17037818180358704387610653 6389181817634514145353995)
                ·
                  refine ⟨9583772726451771218030993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6389181817634514145353995 9583772726451771218030993)
                  ·
                    refine ⟨7187829544838828413523245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9583772726451771218030993 7187829544838828413523245)
                    ·
                      refine ⟨2695436079314560655071217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7187829544838828413523245 2695436079314560655071217)
                      ·
                        rfl

theorem cell23_5249343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 3, 1, 2, 3].length) (baseStart_5249343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5249343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5249343 prefixEnd_5249343 := by exact prefixLift 5249343
  have htrace : WordTrace (prefixWord ++ tailWord_5249343) baseStart_5249343 baseEnd_5249343 := by
    simpa [prefixWord, tailWord_5249343, baseEnd_5249343] using wordTrace_append hprefix tailTrace_5249343
  have hstable : (prefixWord ++ tailWord_5249343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5249343).length < 2 ^ (prefixWord ++ tailWord_5249343).sum := by decide
  have hdescent : baseEnd_5249343 < baseStart_5249343 := by decide
  rcases family_descends (prefixWord ++ tailWord_5249343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5249349 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 4, 2, 6]
def baseStart_5249349 : Nat := 118140960795 + 5249349 * 2 ^ 59
def prefixEnd_5249349 : Nat := 4983230072969 + 3 ^ 40 * 5249349 * 2
def baseEnd_5249349 : Nat := 2695439160198487631596189

theorem tailTrace_5249349 : CollatzResearch.WordTrace tailWord_5249349 prefixEnd_5249349 2695439160198487631596189 := by
  unfold tailWord_5249349
  simp only [CollatzResearch.WordTrace]
  refine ⟨191459487059512565278911101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127639658039675043519274067 191459487059512565278911101)
  ·
    refine ⟨71797307647317211979591663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191459487059512565278911101 71797307647317211979591663)
    ·
      refine ⟨107695961470975817969387495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71797307647317211979591663 107695961470975817969387495)
      ·
        refine ⟨161543942206463726954081243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107695961470975817969387495 161543942206463726954081243)
        ·
          refine ⟨242315913309695590431121865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161543942206463726954081243 242315913309695590431121865)
          ·
            refine ⟨181736934982271692823341399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 242315913309695590431121865 181736934982271692823341399)
            ·
              refine ⟨272605402473407539235012099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181736934982271692823341399 272605402473407539235012099)
              ·
                refine ⟨408908103710111308852518149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 272605402473407539235012099 408908103710111308852518149)
                ·
                  refine ⟨76670269445645870409847153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 408908103710111308852518149 76670269445645870409847153)
                  ·
                    refine ⟨57502702084234402807385365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 76670269445645870409847153 57502702084234402807385365)
                    ·
                      refine ⟨2695439160198487631596189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57502702084234402807385365 2695439160198487631596189)
                      ·
                        rfl

theorem cell23_5249349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 2, 6].length) (baseStart_5249349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5249349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5249349 prefixEnd_5249349 := by exact prefixLift 5249349
  have htrace : WordTrace (prefixWord ++ tailWord_5249349) baseStart_5249349 baseEnd_5249349 := by
    simpa [prefixWord, tailWord_5249349, baseEnd_5249349] using wordTrace_append hprefix tailTrace_5249349
  have hstable : (prefixWord ++ tailWord_5249349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5249349).length < 2 ^ (prefixWord ++ tailWord_5249349).sum := by decide
  have hdescent : baseEnd_5249349 < baseStart_5249349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5249349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5249359 : List Nat := [1, 1, 2, 1, 1, 2, 1, 5, 2, 7]
def baseStart_5249359 : Nat := 118140960795 + 5249359 * 2 ^ 59
def prefixEnd_5249359 : Nat := 4983230072969 + 3 ^ 40 * 5249359 * 2
def baseEnd_5249359 : Nat := 898481431668344197490381

theorem tailTrace_5249359 : CollatzResearch.WordTrace tailWord_5249359 prefixEnd_5249359 898481431668344197490381 := by
  unfold tailWord_5249359
  simp only [CollatzResearch.WordTrace]
  refine ⟨191459851789476336986775131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127639901192984224657850087 191459851789476336986775131)
  ·
    refine ⟨287189777684214505480162697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191459851789476336986775131 287189777684214505480162697)
    ·
      refine ⟨215392333263160879110122023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287189777684214505480162697 215392333263160879110122023)
      ·
        refine ⟨323088499894741318665183035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215392333263160879110122023 323088499894741318665183035)
        ·
          refine ⟨484632749842111977997774553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323088499894741318665183035 484632749842111977997774553)
          ·
            refine ⟨363474562381583983498330915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 484632749842111977997774553 363474562381583983498330915)
            ·
              refine ⟨545211843572375975247496373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 363474562381583983498330915 545211843572375975247496373)
              ·
                refine ⟨51113610334910247679452785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 545211843572375975247496373 51113610334910247679452785)
                ·
                  refine ⟨38335207751182685759589589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51113610334910247679452785 38335207751182685759589589)
                  ·
                    refine ⟨898481431668344197490381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38335207751182685759589589 898481431668344197490381)
                    ·
                      rfl

theorem cell23_5249359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 7].length) (baseStart_5249359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5249359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5249359 prefixEnd_5249359 := by exact prefixLift 5249359
  have htrace : WordTrace (prefixWord ++ tailWord_5249359) baseStart_5249359 baseEnd_5249359 := by
    simpa [prefixWord, tailWord_5249359, baseEnd_5249359] using wordTrace_append hprefix tailTrace_5249359
  have hstable : (prefixWord ++ tailWord_5249359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5249359).length < 2 ^ (prefixWord ++ tailWord_5249359).sum := by decide
  have hdescent : baseEnd_5249359 < baseStart_5249359 := by decide
  rcases family_descends (prefixWord ++ tailWord_5249359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5249416 : List Nat := [2, 1, 3, 3, 1, 1, 1, 2, 1, 3, 5]
def baseStart_5249416 : Nat := 118140960795 + 5249416 * 2 ^ 59
def prefixEnd_5249416 : Nat := 4983230072969 + 3 ^ 40 * 5249416 * 2
def baseEnd_5249416 : Nat := 2695473563402338869458381

theorem tailTrace_5249416 : CollatzResearch.WordTrace tailWord_5249416 prefixEnd_5249416 2695473563402338869458381 := by
  unfold tailWord_5249416
  simp only [CollatzResearch.WordTrace]
  refine ⟨95730965375134917860800051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127641287166846557147733401 95730965375134917860800051)
  ·
    refine ⟨143596448062702376791200077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95730965375134917860800051 143596448062702376791200077)
    ·
      refine ⟨53848668023513391296700029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143596448062702376791200077 53848668023513391296700029)
      ·
        refine ⟨20193250508817521736262511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53848668023513391296700029 20193250508817521736262511)
        ·
          refine ⟨30289875763226282604393767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20193250508817521736262511 30289875763226282604393767)
          ·
            refine ⟨45434813644839423906590651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30289875763226282604393767 45434813644839423906590651)
            ·
              refine ⟨68152220467259135859885977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45434813644839423906590651 68152220467259135859885977)
              ·
                refine ⟨51114165350444351894914483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68152220467259135859885977 51114165350444351894914483)
                ·
                  refine ⟨76671248025666527842371725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51114165350444351894914483 76671248025666527842371725)
                  ·
                    refine ⟨28751718009624947940889397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 76671248025666527842371725 28751718009624947940889397)
                    ·
                      refine ⟨2695473563402338869458381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28751718009624947940889397 2695473563402338869458381)
                      ·
                        rfl

theorem cell23_5249416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_5249416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5249416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5249416 prefixEnd_5249416 := by exact prefixLift 5249416
  have htrace : WordTrace (prefixWord ++ tailWord_5249416) baseStart_5249416 baseEnd_5249416 := by
    simpa [prefixWord, tailWord_5249416, baseEnd_5249416] using wordTrace_append hprefix tailTrace_5249416
  have hstable : (prefixWord ++ tailWord_5249416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5249416).length < 2 ^ (prefixWord ++ tailWord_5249416).sum := by decide
  have hdescent : baseEnd_5249416 < baseStart_5249416 := by decide
  rcases family_descends (prefixWord ++ tailWord_5249416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5249503 : List Nat := [1, 1, 2, 3, 3, 3, 1, 1, 1, 3, 4]
def baseStart_5249503 : Nat := 118140960795 + 5249503 * 2 ^ 59
def prefixEnd_5249503 : Nat := 4983230072969 + 3 ^ 40 * 5249503 * 2
def baseEnd_5249503 : Nat := 2695518236219280029070481

theorem tailTrace_5249503 : CollatzResearch.WordTrace tailWord_5249503 prefixEnd_5249503 2695518236219280029070481 := by
  unfold tailWord_5249503
  simp only [CollatzResearch.WordTrace]
  refine ⟨191465103900954649580017163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127643402600636433053344775 191465103900954649580017163)
  ·
    refine ⟨287197655851431974370025745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191465103900954649580017163 287197655851431974370025745)
    ·
      refine ⟨215398241888573980777519309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287197655851431974370025745 215398241888573980777519309)
      ·
        refine ⟨80774340708215242791569741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 215398241888573980777519309 80774340708215242791569741)
        ·
          refine ⟨30290377765580716046838653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80774340708215242791569741 30290377765580716046838653)
          ·
            refine ⟨11358891662092768517564495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30290377765580716046838653 11358891662092768517564495)
            ·
              refine ⟨17038337493139152776346743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11358891662092768517564495 17038337493139152776346743)
              ·
                refine ⟨25557506239708729164520115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17038337493139152776346743 25557506239708729164520115)
                ·
                  refine ⟨38336259359563093746780173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25557506239708729164520115 38336259359563093746780173)
                  ·
                    refine ⟨14376097259836160155042565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38336259359563093746780173 14376097259836160155042565)
                    ·
                      refine ⟨2695518236219280029070481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14376097259836160155042565 2695518236219280029070481)
                      ·
                        rfl

theorem cell23_5249503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 3, 4].length) (baseStart_5249503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5249503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5249503 prefixEnd_5249503 := by exact prefixLift 5249503
  have htrace : WordTrace (prefixWord ++ tailWord_5249503) baseStart_5249503 baseEnd_5249503 := by
    simpa [prefixWord, tailWord_5249503, baseEnd_5249503] using wordTrace_append hprefix tailTrace_5249503
  have hstable : (prefixWord ++ tailWord_5249503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5249503).length < 2 ^ (prefixWord ++ tailWord_5249503).sum := by decide
  have hdescent : baseEnd_5249503 < baseStart_5249503 := by decide
  rcases family_descends (prefixWord ++ tailWord_5249503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5249516 : List Nat := [2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 6]
def baseStart_5249516 : Nat := 118140960795 + 5249516 * 2 ^ 59
def prefixEnd_5249516 : Nat := 4983230072969 + 3 ^ 40 * 5249516 * 2
def baseEnd_5249516 : Nat := 2695524911467788478207921

theorem tailTrace_5249516 : CollatzResearch.WordTrace tailWord_5249516 prefixEnd_5249516 2695524911467788478207921 := by
  unfold tailWord_5249516
  simp only [CollatzResearch.WordTrace]
  refine ⟨95732789024953776400120201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127643718699938368533493601 95732789024953776400120201)
  ·
    refine ⟨71799591768715332300090151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95732789024953776400120201 71799591768715332300090151)
    ·
      refine ⟨107699387653072998450135227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71799591768715332300090151 107699387653072998450135227)
      ·
        refine ⟨161549081479609497675202841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107699387653072998450135227 161549081479609497675202841)
        ·
          refine ⟨121161811109707123256402131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161549081479609497675202841 121161811109707123256402131)
          ·
            refine ⟨181742716664560684884603197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121161811109707123256402131 181742716664560684884603197)
            ·
              refine ⟨68153518749210256831726199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 181742716664560684884603197 68153518749210256831726199)
              ·
                refine ⟨102230278123815385247589299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68153518749210256831726199 102230278123815385247589299)
                ·
                  refine ⟨153345417185723077871383949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102230278123815385247589299 153345417185723077871383949)
                  ·
                    refine ⟨57504531444646154201768981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 153345417185723077871383949 57504531444646154201768981)
                    ·
                      refine ⟨2695524911467788478207921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57504531444646154201768981 2695524911467788478207921)
                      ·
                        rfl

theorem cell23_5249516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 6].length) (baseStart_5249516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5249516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5249516 prefixEnd_5249516 := by exact prefixLift 5249516
  have htrace : WordTrace (prefixWord ++ tailWord_5249516) baseStart_5249516 baseEnd_5249516 := by
    simpa [prefixWord, tailWord_5249516, baseEnd_5249516] using wordTrace_append hprefix tailTrace_5249516
  have hstable : (prefixWord ++ tailWord_5249516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5249516).length < 2 ^ (prefixWord ++ tailWord_5249516).sum := by decide
  have hdescent : baseEnd_5249516 < baseStart_5249516 := by decide
  rcases family_descends (prefixWord ++ tailWord_5249516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5249523 : List Nat := [1, 1, 1, 2, 2, 2, 4, 1, 4, 2, 3]
def baseStart_5249523 : Nat := 118140960795 + 5249523 * 2 ^ 59
def prefixEnd_5249523 : Nat := 4983230072969 + 3 ^ 40 * 5249523 * 2
def baseEnd_5249523 : Nat := 2695528505832369950820389

theorem tailTrace_5249523 : CollatzResearch.WordTrace tailWord_5249523 prefixEnd_5249523 2695528505832369950820389 := by
  unfold tailWord_5249523
  simp only [CollatzResearch.WordTrace]
  refine ⟨191465833360882192995745223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127643888907254795330496815 191465833360882192995745223)
  ·
    refine ⟨287198750041323289493617835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191465833360882192995745223 287198750041323289493617835)
    ·
      refine ⟨430798125061984934240426753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287198750041323289493617835 430798125061984934240426753)
      ·
        refine ⟨323098593796488700680320065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 430798125061984934240426753 323098593796488700680320065)
        ·
          refine ⟨242323945347366525510240049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 323098593796488700680320065 242323945347366525510240049)
          ·
            refine ⟨181742959010524894132680037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 242323945347366525510240049 181742959010524894132680037)
            ·
              refine ⟨34076804814473417649877507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 181742959010524894132680037 34076804814473417649877507)
              ·
                refine ⟨51115207221710126474816261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34076804814473417649877507 51115207221710126474816261)
                ·
                  refine ⟨9584101354070648714028049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51115207221710126474816261 9584101354070648714028049)
                  ·
                    refine ⟨7188076015552986535521037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9584101354070648714028049 7188076015552986535521037)
                    ·
                      refine ⟨2695528505832369950820389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7188076015552986535521037 2695528505832369950820389)
                      ·
                        rfl

theorem cell23_5249523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 4, 2, 3].length) (baseStart_5249523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5249523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5249523 prefixEnd_5249523 := by exact prefixLift 5249523
  have htrace : WordTrace (prefixWord ++ tailWord_5249523) baseStart_5249523 baseEnd_5249523 := by
    simpa [prefixWord, tailWord_5249523, baseEnd_5249523] using wordTrace_append hprefix tailTrace_5249523
  have hstable : (prefixWord ++ tailWord_5249523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5249523).length < 2 ^ (prefixWord ++ tailWord_5249523).sum := by decide
  have hdescent : baseEnd_5249523 < baseStart_5249523 := by decide
  rcases family_descends (prefixWord ++ tailWord_5249523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5249540 : List Nat := [2, 3, 2, 3, 1, 1, 1, 2, 1, 4, 3]
def baseStart_5249540 : Nat := 118140960795 + 5249540 * 2 ^ 59
def prefixEnd_5249540 : Nat := 4983230072969 + 3 ^ 40 * 5249540 * 2
def baseEnd_5249540 : Nat := 2695537235003496384307811

theorem tailTrace_5249540 : CollatzResearch.WordTrace tailWord_5249540 prefixEnd_5249540 2695537235003496384307811 := by
  unfold tailWord_5249540
  simp only [CollatzResearch.WordTrace]
  refine ⟨95733226700910302449557037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127644302267880403266076049 95733226700910302449557037)
  ·
    refine ⟨35899960012841363418583889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95733226700910302449557037 35899960012841363418583889)
    ·
      refine ⟨26924970009631022563937917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35899960012841363418583889 26924970009631022563937917)
      ·
        refine ⟨10096863753611633461476719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26924970009631022563937917 10096863753611633461476719)
        ·
          refine ⟨15145295630417450192215079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10096863753611633461476719 15145295630417450192215079)
          ·
            refine ⟨22717943445626175288322619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15145295630417450192215079 22717943445626175288322619)
            ·
              refine ⟨34076915168439262932483929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22717943445626175288322619 34076915168439262932483929)
              ·
                refine ⟨25557686376329447199362947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34076915168439262932483929 25557686376329447199362947)
                ·
                  refine ⟨38336529564494170799044421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25557686376329447199362947 38336529564494170799044421)
                  ·
                    refine ⟨7188099293342657024820829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38336529564494170799044421 7188099293342657024820829)
                    ·
                      refine ⟨2695537235003496384307811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7188099293342657024820829 2695537235003496384307811)
                      ·
                        rfl

theorem cell23_5249540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_5249540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5249540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5249540 prefixEnd_5249540 := by exact prefixLift 5249540
  have htrace : WordTrace (prefixWord ++ tailWord_5249540) baseStart_5249540 baseEnd_5249540 := by
    simpa [prefixWord, tailWord_5249540, baseEnd_5249540] using wordTrace_append hprefix tailTrace_5249540
  have hstable : (prefixWord ++ tailWord_5249540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5249540).length < 2 ^ (prefixWord ++ tailWord_5249540).sum := by decide
  have hdescent : baseEnd_5249540 < baseStart_5249540 := by decide
  rcases family_descends (prefixWord ++ tailWord_5249540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5249564 : List Nat := [2, 2, 3, 1, 2, 4, 1, 3, 1, 4]
def baseStart_5249564 : Nat := 118140960795 + 5249564 * 2 ^ 59
def prefixEnd_5249564 : Nat := 4983230072969 + 3 ^ 40 * 5249564 * 2
def baseEnd_5249564 : Nat := 898516519513068096802567

theorem tailTrace_5249564 : CollatzResearch.WordTrace tailWord_5249564 prefixEnd_5249564 898516519513068096802567 := by
  unfold tailWord_5249564
  simp only [CollatzResearch.WordTrace]
  refine ⟨95733664376866828498993873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127644885835822437998658497 95733664376866828498993873)
  ·
    refine ⟨71800248282650121374245405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95733664376866828498993873 71800248282650121374245405)
    ·
      refine ⟨26925093105993795515342027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71800248282650121374245405 26925093105993795515342027)
      ·
        refine ⟨40387639658990693273013041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26925093105993795515342027 40387639658990693273013041)
        ·
          refine ⟨30290729744243019954759781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40387639658990693273013041 30290729744243019954759781)
          ·
            refine ⟨5679511827045566241517459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30290729744243019954759781 5679511827045566241517459)
            ·
              refine ⟨8519267740568349362276189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5679511827045566241517459 8519267740568349362276189)
              ·
                refine ⟨3194725402713131010853571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8519267740568349362276189 3194725402713131010853571)
                ·
                  refine ⟨4792088104069696516280357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3194725402713131010853571 4792088104069696516280357)
                  ·
                    refine ⟨898516519513068096802567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4792088104069696516280357 898516519513068096802567)
                    ·
                      rfl

theorem cell23_5249564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 3, 1, 4].length) (baseStart_5249564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5249564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5249564 prefixEnd_5249564 := by exact prefixLift 5249564
  have htrace : WordTrace (prefixWord ++ tailWord_5249564) baseStart_5249564 baseEnd_5249564 := by
    simpa [prefixWord, tailWord_5249564, baseEnd_5249564] using wordTrace_append hprefix tailTrace_5249564
  have hstable : (prefixWord ++ tailWord_5249564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5249564).length < 2 ^ (prefixWord ++ tailWord_5249564).sum := by decide
  have hdescent : baseEnd_5249564 < baseStart_5249564 := by decide
  rcases family_descends (prefixWord ++ tailWord_5249564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5249607 : List Nat := [1, 1, 4, 1, 4, 3, 1, 2, 1, 5]
def baseStart_5249607 : Nat := 118140960795 + 5249607 * 2 ^ 59
def prefixEnd_5249607 : Nat := 4983230072969 + 3 ^ 40 * 5249607 * 2
def baseEnd_5249607 : Nat := 898523879402449207390001

theorem tailTrace_5249607 : CollatzResearch.WordTrace tailWord_5249607 prefixEnd_5249607 898523879402449207390001 := by
  unfold tailWord_5249607
  simp only [CollatzResearch.WordTrace]
  refine ⟨191468897092577875341803075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127645931395051916894535383 191468897092577875341803075)
  ·
    refine ⟨287203345638866813012704613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191468897092577875341803075 287203345638866813012704613)
    ·
      refine ⟨53850627307287527439882115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 287203345638866813012704613 53850627307287527439882115)
      ·
        refine ⟨80775940960931291159823173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53850627307287527439882115 80775940960931291159823173)
        ·
          refine ⟨15145488930174617092466845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80775940960931291159823173 15145488930174617092466845)
          ·
            refine ⟨5679558348815481409675067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15145488930174617092466845 5679558348815481409675067)
            ·
              refine ⟨8519337523223222114512601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5679558348815481409675067 8519337523223222114512601)
              ·
                refine ⟨6389503142417416585884451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8519337523223222114512601 6389503142417416585884451)
                ·
                  refine ⟨9584254713626124878826677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6389503142417416585884451 9584254713626124878826677)
                  ·
                    refine ⟨898523879402449207390001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9584254713626124878826677 898523879402449207390001)
                    ·
                      rfl

theorem cell23_5249607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 2, 1, 5].length) (baseStart_5249607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5249607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5249607 prefixEnd_5249607 := by exact prefixLift 5249607
  have htrace : WordTrace (prefixWord ++ tailWord_5249607) baseStart_5249607 baseEnd_5249607 := by
    simpa [prefixWord, tailWord_5249607, baseEnd_5249607] using wordTrace_append hprefix tailTrace_5249607
  have hstable : (prefixWord ++ tailWord_5249607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5249607).length < 2 ^ (prefixWord ++ tailWord_5249607).sum := by decide
  have hdescent : baseEnd_5249607 < baseStart_5249607 := by decide
  rcases family_descends (prefixWord ++ tailWord_5249607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5249610 : List Nat := [3, 1, 2, 1, 1, 5, 1, 1, 3, 1, 4]
def baseStart_5249610 : Nat := 118140960795 + 5249610 * 2 ^ 59
def prefixEnd_5249610 : Nat := 4983230072969 + 3 ^ 40 * 5249610 * 2
def baseEnd_5249610 : Nat := 2695573178649311110432489

theorem tailTrace_5249610 : CollatzResearch.WordTrace tailWord_5249610 prefixEnd_5249610 2695573178649311110432489 := by
  unfold tailWord_5249610
  simp only [CollatzResearch.WordTrace]
  refine ⟨47867251627891751713540571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127646004341044671236108189 47867251627891751713540571)
  ·
    refine ⟨71800877441837627570310857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47867251627891751713540571 71800877441837627570310857)
    ·
      refine ⟨53850658081378220677733143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71800877441837627570310857 53850658081378220677733143)
      ·
        refine ⟨80775987122067331016599715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53850658081378220677733143 80775987122067331016599715)
        ·
          refine ⟨121163980683100996524899573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80775987122067331016599715 121163980683100996524899573)
          ·
            refine ⟨11359123189040718424209335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 121163980683100996524899573 11359123189040718424209335)
            ·
              refine ⟨17038684783561077636314003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11359123189040718424209335 17038684783561077636314003)
              ·
                refine ⟨25558027175341616454471005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17038684783561077636314003 25558027175341616454471005)
                ·
                  refine ⟨9584260190753106170426627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25558027175341616454471005 9584260190753106170426627)
                  ·
                    refine ⟨14376390286129659255639941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9584260190753106170426627 14376390286129659255639941)
                    ·
                      refine ⟨2695573178649311110432489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14376390286129659255639941 2695573178649311110432489)
                      ·
                        rfl

theorem cell23_5249610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 3, 1, 4].length) (baseStart_5249610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5249610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5249610 prefixEnd_5249610 := by exact prefixLift 5249610
  have htrace : WordTrace (prefixWord ++ tailWord_5249610) baseStart_5249610 baseEnd_5249610 := by
    simpa [prefixWord, tailWord_5249610, baseEnd_5249610] using wordTrace_append hprefix tailTrace_5249610
  have hstable : (prefixWord ++ tailWord_5249610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5249610).length < 2 ^ (prefixWord ++ tailWord_5249610).sum := by decide
  have hdescent : baseEnd_5249610 < baseStart_5249610 := by decide
  rcases family_descends (prefixWord ++ tailWord_5249610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5249620 : List Nat := [2, 4, 1, 1, 1, 4, 1, 2, 1, 6]
def baseStart_5249620 : Nat := 118140960795 + 5249620 * 2 ^ 59
def prefixEnd_5249620 : Nat := 4983230072969 + 3 ^ 40 * 5249620 * 2
def baseEnd_5249620 : Nat := 898526104485285357102481

theorem tailTrace_5249620 : CollatzResearch.WordTrace tailWord_5249620 prefixEnd_5249620 898526104485285357102481 := by
  unfold tailWord_5249620
  simp only [CollatzResearch.WordTrace]
  refine ⟨95734685620765389281013157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127646247494353852374684209 95734685620765389281013157)
  ·
    refine ⟨17950253553893510490189967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95734685620765389281013157 17950253553893510490189967)
    ·
      refine ⟨26925380330840265735284951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17950253553893510490189967 26925380330840265735284951)
      ·
        refine ⟨40388070496260398602927427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26925380330840265735284951 40388070496260398602927427)
        ·
          refine ⟨60582105744390597904391141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40388070496260398602927427 60582105744390597904391141)
          ·
            refine ⟨11359144827073237107073339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60582105744390597904391141 11359144827073237107073339)
            ·
              refine ⟨17038717240609855660610009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11359144827073237107073339 17038717240609855660610009)
              ·
                refine ⟨12779037930457391745457507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17038717240609855660610009 12779037930457391745457507)
                ·
                  refine ⟨19168556895686087618186261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12779037930457391745457507 19168556895686087618186261)
                  ·
                    refine ⟨898526104485285357102481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19168556895686087618186261 898526104485285357102481)
                    ·
                      rfl

theorem cell23_5249620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_5249620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5249620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5249620 prefixEnd_5249620 := by exact prefixLift 5249620
  have htrace : WordTrace (prefixWord ++ tailWord_5249620) baseStart_5249620 baseEnd_5249620 := by
    simpa [prefixWord, tailWord_5249620, baseEnd_5249620] using wordTrace_append hprefix tailTrace_5249620
  have hstable : (prefixWord ++ tailWord_5249620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5249620).length < 2 ^ (prefixWord ++ tailWord_5249620).sum := by decide
  have hdescent : baseEnd_5249620 < baseStart_5249620 := by decide
  rcases family_descends (prefixWord ++ tailWord_5249620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5249660 : List Nat := [2, 2, 2, 1, 1, 2, 3, 3, 1, 3, 3]
def baseStart_5249660 : Nat := 118140960795 + 5249660 * 2 ^ 59
def prefixEnd_5249660 : Nat := 4983230072969 + 3 ^ 40 * 5249660 * 2
def baseEnd_5249660 : Nat := 2695598852682035914807259

theorem tailTrace_5249660 : CollatzResearch.WordTrace tailWord_5249660 prefixEnd_5249660 2695598852682035914807259 := by
  unfold tailWord_5249660
  simp only [CollatzResearch.WordTrace]
  refine ⟨95735415080692932696741217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127647220107590576928988289 95735415080692932696741217)
  ·
    refine ⟨71801561310519699522555913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95735415080692932696741217 71801561310519699522555913)
    ·
      refine ⟨53851170982889774641916935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71801561310519699522555913 53851170982889774641916935)
      ·
        refine ⟨80776756474334661962875403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53851170982889774641916935 80776756474334661962875403)
        ·
          refine ⟨121165134711501992944313105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80776756474334661962875403 121165134711501992944313105)
          ·
            refine ⟨90873851033626494708234829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121165134711501992944313105 90873851033626494708234829)
            ·
              refine ⟨34077694137609935515588061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90873851033626494708234829 34077694137609935515588061)
              ·
                refine ⟨12779135301603725818345523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34077694137609935515588061 12779135301603725818345523)
                ·
                  refine ⟨19168702952405588727518285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12779135301603725818345523 19168702952405588727518285)
                  ·
                    refine ⟨7188263607152095772819357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19168702952405588727518285 7188263607152095772819357)
                    ·
                      refine ⟨2695598852682035914807259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7188263607152095772819357 2695598852682035914807259)
                      ·
                        rfl

theorem cell23_5249660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 3, 1, 3, 3].length) (baseStart_5249660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5249660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5249660 prefixEnd_5249660 := by exact prefixLift 5249660
  have htrace : WordTrace (prefixWord ++ tailWord_5249660) baseStart_5249660 baseEnd_5249660 := by
    simpa [prefixWord, tailWord_5249660, baseEnd_5249660] using wordTrace_append hprefix tailTrace_5249660
  have hstable : (prefixWord ++ tailWord_5249660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5249660).length < 2 ^ (prefixWord ++ tailWord_5249660).sum := by decide
  have hdescent : baseEnd_5249660 < baseStart_5249660 := by decide
  rcases family_descends (prefixWord ++ tailWord_5249660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5249673 : List Nat := [1, 2, 1, 1, 4, 1, 1, 3, 2, 2, 5]
def baseStart_5249673 : Nat := 118140960795 + 5249673 * 2 ^ 59
def prefixEnd_5249673 : Nat := 4983230072969 + 3 ^ 40 * 5249673 * 2
def baseEnd_5249673 : Nat := 2695605527930544363944699

theorem tailTrace_5249673 : CollatzResearch.WordTrace tailWord_5249673 prefixEnd_5249673 2695605527930544363944699 := by
  unfold tailWord_5249673
  simp only [CollatzResearch.WordTrace]
  refine ⟨191471304310338768613705673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127647536206892512409137115 191471304310338768613705673)
  ·
    refine ⟨143603478232754076460279255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191471304310338768613705673 143603478232754076460279255)
    ·
      refine ⟨215405217349131114690418883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143603478232754076460279255 215405217349131114690418883)
      ·
        refine ⟨323107826023696672035628325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215405217349131114690418883 323107826023696672035628325)
        ·
          refine ⟨60582717379443126006680311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 323107826023696672035628325 60582717379443126006680311)
          ·
            refine ⟨90874076069164689010020467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60582717379443126006680311 90874076069164689010020467)
            ·
              refine ⟨136311114103747033515030701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90874076069164689010020467 136311114103747033515030701)
              ·
                refine ⟨51116667788905137568136513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 136311114103747033515030701 51116667788905137568136513)
                ·
                  refine ⟨38337500841678853176102385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51116667788905137568136513 38337500841678853176102385)
                  ·
                    refine ⟨28753125631259139882076789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38337500841678853176102385 28753125631259139882076789)
                    ·
                      refine ⟨2695605527930544363944699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28753125631259139882076789 2695605527930544363944699)
                      ·
                        rfl

theorem cell23_5249673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 2, 5].length) (baseStart_5249673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5249673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5249673 prefixEnd_5249673 := by exact prefixLift 5249673
  have htrace : WordTrace (prefixWord ++ tailWord_5249673) baseStart_5249673 baseEnd_5249673 := by
    simpa [prefixWord, tailWord_5249673, baseEnd_5249673] using wordTrace_append hprefix tailTrace_5249673
  have hstable : (prefixWord ++ tailWord_5249673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5249673).length < 2 ^ (prefixWord ++ tailWord_5249673).sum := by decide
  have hdescent : baseEnd_5249673 < baseStart_5249673 := by decide
  rcases family_descends (prefixWord ++ tailWord_5249673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5249683 : List Nat := [1, 1, 1, 2, 1, 2, 2, 2, 4, 3, 4]
def baseStart_5249683 : Nat := 118140960795 + 5249683 * 2 ^ 59
def prefixEnd_5249683 : Nat := 4983230072969 + 3 ^ 40 * 5249683 * 2
def baseEnd_5249683 : Nat := 2695610662737089324819653

theorem tailTrace_5249683 : CollatzResearch.WordTrace tailWord_5249683 prefixEnd_5249683 2695610662737089324819653 := by
  unfold tailWord_5249683
  simp only [CollatzResearch.WordTrace]
  refine ⟨191471669040302540321569703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127647779360201693547713135 191471669040302540321569703)
  ·
    refine ⟨287207503560453810482354555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191471669040302540321569703 287207503560453810482354555)
    ·
      refine ⟨430811255340680715723531833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287207503560453810482354555 430811255340680715723531833)
      ·
        refine ⟨323108441505510536792648875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 430811255340680715723531833 323108441505510536792648875)
        ·
          refine ⟨484662662258265805188973313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323108441505510536792648875 484662662258265805188973313)
          ·
            refine ⟨363496996693699353891729985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 484662662258265805188973313 363496996693699353891729985)
            ·
              refine ⟨272622747520274515418797489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 363496996693699353891729985 272622747520274515418797489)
              ·
                refine ⟨204467060640205886564098117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 272622747520274515418797489 204467060640205886564098117)
                ·
                  refine ⟨38337573870038603730768397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 204467060640205886564098117 38337573870038603730768397)
                  ·
                    refine ⟨14376590201264476399038149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38337573870038603730768397 14376590201264476399038149)
                    ·
                      refine ⟨2695610662737089324819653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14376590201264476399038149 2695610662737089324819653)
                      ·
                        rfl

theorem cell23_5249683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 3, 4].length) (baseStart_5249683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5249683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5249683 prefixEnd_5249683 := by exact prefixLift 5249683
  have htrace : WordTrace (prefixWord ++ tailWord_5249683) baseStart_5249683 baseEnd_5249683 := by
    simpa [prefixWord, tailWord_5249683, baseEnd_5249683] using wordTrace_append hprefix tailTrace_5249683
  have hstable : (prefixWord ++ tailWord_5249683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5249683).length < 2 ^ (prefixWord ++ tailWord_5249683).sum := by decide
  have hdescent : baseEnd_5249683 < baseStart_5249683 := by decide
  rcases family_descends (prefixWord ++ tailWord_5249683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5249694 : List Nat := [4, 3, 1, 1, 1, 1, 3, 1, 4, 1, 3]
def baseStart_5249694 : Nat := 118140960795 + 5249694 * 2 ^ 59
def prefixEnd_5249694 : Nat := 4983230072969 + 3 ^ 40 * 5249694 * 2
def baseEnd_5249694 : Nat := 2695616311024288781782103

theorem tailTrace_5249694 : CollatzResearch.WordTrace tailWord_5249694 prefixEnd_5249694 2695616311024288781782103 := by
  unfold tailWord_5249694
  simp only [CollatzResearch.WordTrace]
  refine ⟨23934008780407836150027517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127648046828841792800146757 23934008780407836150027517)
  ·
    refine ⟨8975253292652938556260319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23934008780407836150027517 8975253292652938556260319)
    ·
      refine ⟨13462879938979407834390479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8975253292652938556260319 13462879938979407834390479)
      ·
        refine ⟨20194319908469111751585719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13462879938979407834390479 20194319908469111751585719)
        ·
          refine ⟨30291479862703667627378579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20194319908469111751585719 30291479862703667627378579)
          ·
            refine ⟨45437219794055501441067869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30291479862703667627378579 45437219794055501441067869)
            ·
              refine ⟨17038957422770813040400451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45437219794055501441067869 17038957422770813040400451)
              ·
                refine ⟨25558436134156219560600677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17038957422770813040400451 25558436134156219560600677)
                ·
                  refine ⟨4792206775154291167612627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25558436134156219560600677 4792206775154291167612627)
                  ·
                    refine ⟨7188310162731436751418941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4792206775154291167612627 7188310162731436751418941)
                    ·
                      refine ⟨2695616311024288781782103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7188310162731436751418941 2695616311024288781782103)
                      ·
                        rfl

theorem cell23_5249694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_5249694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5249694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5249694 prefixEnd_5249694 := by exact prefixLift 5249694
  have htrace : WordTrace (prefixWord ++ tailWord_5249694) baseStart_5249694 baseEnd_5249694 := by
    simpa [prefixWord, tailWord_5249694, baseEnd_5249694] using wordTrace_append hprefix tailTrace_5249694
  have hstable : (prefixWord ++ tailWord_5249694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5249694).length < 2 ^ (prefixWord ++ tailWord_5249694).sum := by decide
  have hdescent : baseEnd_5249694 < baseStart_5249694 := by decide
  rcases family_descends (prefixWord ++ tailWord_5249694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5249733 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 3, 2, 7]
def baseStart_5249733 : Nat := 118140960795 + 5249733 * 2 ^ 59
def prefixEnd_5249733 : Nat := 4983230072969 + 3 ^ 40 * 5249733 * 2
def baseEnd_5249733 : Nat := 2695636336769814129194423

theorem tailTrace_5249733 : CollatzResearch.WordTrace tailWord_5249733 prefixEnd_5249733 2695636336769814129194423 := by
  unfold tailWord_5249733
  simp only [CollatzResearch.WordTrace]
  refine ⟨191473492690121398860889853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127648995126747599240593235 191473492690121398860889853)
  ·
    refine ⟨71802559758795524572833695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191473492690121398860889853 71802559758795524572833695)
    ·
      refine ⟨107703839638193286859250543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71802559758795524572833695 107703839638193286859250543)
      ·
        refine ⟨161555759457289930288875815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107703839638193286859250543 161555759457289930288875815)
        ·
          refine ⟨242333639185934895433313723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161555759457289930288875815 242333639185934895433313723)
          ·
            refine ⟨363500458778902343149970585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242333639185934895433313723 363500458778902343149970585)
            ·
              refine ⟨272625344084176757362477939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 363500458778902343149970585 272625344084176757362477939)
              ·
                refine ⟨408938016126265136043716909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 272625344084176757362477939 408938016126265136043716909)
                ·
                  refine ⟨153351756047349426016393841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 408938016126265136043716909 153351756047349426016393841)
                  ·
                    refine ⟨115013817035512069512295381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 153351756047349426016393841 115013817035512069512295381)
                    ·
                      refine ⟨2695636336769814129194423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 115013817035512069512295381 2695636336769814129194423)
                      ·
                        rfl

theorem cell23_5249733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 2, 7].length) (baseStart_5249733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5249733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5249733 prefixEnd_5249733 := by exact prefixLift 5249733
  have htrace : WordTrace (prefixWord ++ tailWord_5249733) baseStart_5249733 baseEnd_5249733 := by
    simpa [prefixWord, tailWord_5249733, baseEnd_5249733] using wordTrace_append hprefix tailTrace_5249733
  have hstable : (prefixWord ++ tailWord_5249733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5249733).length < 2 ^ (prefixWord ++ tailWord_5249733).sum := by decide
  have hdescent : baseEnd_5249733 < baseStart_5249733 := by decide
  rcases family_descends (prefixWord ++ tailWord_5249733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5249743 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 6]
def baseStart_5249743 : Nat := 118140960795 + 5249743 * 2 ^ 59
def prefixEnd_5249743 : Nat := 4983230072969 + 3 ^ 40 * 5249743 * 2
def baseEnd_5249743 : Nat := 2695641471576359090069377

theorem tailTrace_5249743 : CollatzResearch.WordTrace tailWord_5249743 prefixEnd_5249743 2695641471576359090069377 := by
  unfold tailWord_5249743
  simp only [CollatzResearch.WordTrace]
  refine ⟨191473857420085170568753883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127649238280056780379169255 191473857420085170568753883)
  ·
    refine ⟨287210786130127755853130825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191473857420085170568753883 287210786130127755853130825)
    ·
      refine ⟨215408089597595816889848119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287210786130127755853130825 215408089597595816889848119)
      ·
        refine ⟨323112134396393725334772179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215408089597595816889848119 323112134396393725334772179)
        ·
          refine ⟨484668201594590588002158269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323112134396393725334772179 484668201594590588002158269)
          ·
            refine ⟨181750575597971470500809351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 484668201594590588002158269 181750575597971470500809351)
            ·
              refine ⟨272625863396957205751214027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181750575597971470500809351 272625863396957205751214027)
              ·
                refine ⟨408938795095435808626821041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 272625863396957205751214027 408938795095435808626821041)
                ·
                  refine ⟨306704096321576856470115781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 408938795095435808626821041 306704096321576856470115781)
                  ·
                    refine ⟨57507018060295660588146709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 306704096321576856470115781 57507018060295660588146709)
                    ·
                      refine ⟨2695641471576359090069377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57507018060295660588146709 2695641471576359090069377)
                      ·
                        rfl

theorem cell23_5249743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 6].length) (baseStart_5249743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5249743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5249743 prefixEnd_5249743 := by exact prefixLift 5249743
  have htrace : WordTrace (prefixWord ++ tailWord_5249743) baseStart_5249743 baseEnd_5249743 := by
    simpa [prefixWord, tailWord_5249743, baseEnd_5249743] using wordTrace_append hprefix tailTrace_5249743
  have hstable : (prefixWord ++ tailWord_5249743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5249743).length < 2 ^ (prefixWord ++ tailWord_5249743).sum := by decide
  have hdescent : baseEnd_5249743 < baseStart_5249743 := by decide
  rcases family_descends (prefixWord ++ tailWord_5249743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5249770 : List Nat := [3, 1, 3, 1, 1, 1, 1, 1, 6, 5]
def baseStart_5249770 : Nat := 118140960795 + 5249770 * 2 ^ 59
def prefixEnd_5249770 : Nat := 4983230072969 + 3 ^ 40 * 5249770 * 2
def baseEnd_5249770 : Nat := 898551778518010161477251

theorem tailTrace_5249770 : CollatzResearch.WordTrace tailWord_5249770 prefixEnd_5249770 898551778518010161477251 := by
  unfold tailWord_5249770
  simp only [CollatzResearch.WordTrace]
  refine ⟨47868710547746838544996691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127649894793991569453324509 47868710547746838544996691)
  ·
    refine ⟨71803065821620257817495037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47868710547746838544996691 71803065821620257817495037)
    ·
      refine ⟨26926149683107596681560639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71803065821620257817495037 26926149683107596681560639)
      ·
        refine ⟨40389224524661395022340959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26926149683107596681560639 40389224524661395022340959)
        ·
          refine ⟨60583836786992092533511439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40389224524661395022340959 60583836786992092533511439)
          ·
            refine ⟨90875755180488138800267159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60583836786992092533511439 90875755180488138800267159)
            ·
              refine ⟨136313632770732208200400739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90875755180488138800267159 136313632770732208200400739)
              ·
                refine ⟨204470449156098312300601109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136313632770732208200400739 204470449156098312300601109)
                ·
                  refine ⟨9584552304192108389090677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 204470449156098312300601109 9584552304192108389090677)
                  ·
                    refine ⟨898551778518010161477251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9584552304192108389090677 898551778518010161477251)
                    ·
                      rfl

theorem cell23_5249770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_5249770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5249770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5249770 prefixEnd_5249770 := by exact prefixLift 5249770
  have htrace : WordTrace (prefixWord ++ tailWord_5249770) baseStart_5249770 baseEnd_5249770 := by
    simpa [prefixWord, tailWord_5249770, baseEnd_5249770] using wordTrace_append hprefix tailTrace_5249770
  have hstable : (prefixWord ++ tailWord_5249770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5249770).length < 2 ^ (prefixWord ++ tailWord_5249770).sum := by decide
  have hdescent : baseEnd_5249770 < baseStart_5249770 := by decide
  rcases family_descends (prefixWord ++ tailWord_5249770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5249807 : List Nat := [1, 1, 2, 1, 1, 1, 6, 2, 2, 4, 2]
def baseStart_5249807 : Nat := 118140960795 + 5249807 * 2 ^ 59
def prefixEnd_5249807 : Nat := 4983230072969 + 3 ^ 40 * 5249807 * 2
def baseEnd_5249807 : Nat := 2695674334338246839669083

theorem tailTrace_5249807 : CollatzResearch.WordTrace tailWord_5249807 prefixEnd_5249807 2695674334338246839669083 := by
  unfold tailWord_5249807
  simp only [CollatzResearch.WordTrace]
  refine ⟨191476191691853309499083675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127650794461235539666055783 191476191691853309499083675)
  ·
    refine ⟨287214287537779964248625513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191476191691853309499083675 287214287537779964248625513)
    ·
      refine ⟨215410715653334973186469135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287214287537779964248625513 215410715653334973186469135)
      ·
        refine ⟨323116073480002459779703703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215410715653334973186469135 323116073480002459779703703)
        ·
          refine ⟨484674110220003689669555555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323116073480002459779703703 484674110220003689669555555)
          ·
            refine ⟨727011165330005534504333333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 484674110220003689669555555 727011165330005534504333333)
            ·
              refine ⟨34078648374844009429890625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 727011165330005534504333333 34078648374844009429890625)
              ·
                refine ⟨25558986281133007072417969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34078648374844009429890625 25558986281133007072417969)
                ·
                  refine ⟨19169239710849755304313477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25558986281133007072417969 19169239710849755304313477)
                  ·
                    refine ⟨3594232445784329119558777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19169239710849755304313477 3594232445784329119558777)
                    ·
                      refine ⟨2695674334338246839669083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3594232445784329119558777 2695674334338246839669083)
                      ·
                        rfl

theorem cell23_5249807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 2, 4, 2].length) (baseStart_5249807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5249807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5249807 prefixEnd_5249807 := by exact prefixLift 5249807
  have htrace : WordTrace (prefixWord ++ tailWord_5249807) baseStart_5249807 baseEnd_5249807 := by
    simpa [prefixWord, tailWord_5249807, baseEnd_5249807] using wordTrace_append hprefix tailTrace_5249807
  have hstable : (prefixWord ++ tailWord_5249807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5249807).length < 2 ^ (prefixWord ++ tailWord_5249807).sum := by decide
  have hdescent : baseEnd_5249807 < baseStart_5249807 := by decide
  rcases family_descends (prefixWord ++ tailWord_5249807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5249824 : List Nat := [2, 1, 1, 5, 1, 3, 1, 1, 2, 4, 2]
def baseStart_5249824 : Nat := 118140960795 + 5249824 * 2 ^ 59
def prefixEnd_5249824 : Nat := 4983230072969 + 3 ^ 40 * 5249824 * 2
def baseEnd_5249824 : Nat := 2695683063509373273156505

theorem tailTrace_5249824 : CollatzResearch.WordTrace tailWord_5249824 prefixEnd_5249824 2695683063509373273156505 := by
  unfold tailWord_5249824
  simp only [CollatzResearch.WordTrace]
  refine ⟨95738405866395860701226263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127651207821861147601635017 95738405866395860701226263)
  ·
    refine ⟨143607608799593791051839395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95738405866395860701226263 143607608799593791051839395)
    ·
      refine ⟨215411413199390686577759093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143607608799593791051839395 215411413199390686577759093)
      ·
        refine ⟨20194819987442876866664915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 215411413199390686577759093 20194819987442876866664915)
        ·
          refine ⟨30292229981164315299997373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20194819987442876866664915 30292229981164315299997373)
          ·
            refine ⟨11359586242936618237499015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30292229981164315299997373 11359586242936618237499015)
            ·
              refine ⟨17039379364404927356248523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11359586242936618237499015 17039379364404927356248523)
              ·
                refine ⟨25559069046607391034372785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17039379364404927356248523 25559069046607391034372785)
                ·
                  refine ⟨19169301784955543275779589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25559069046607391034372785 19169301784955543275779589)
                  ·
                    refine ⟨3594244084679164364208673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19169301784955543275779589 3594244084679164364208673)
                    ·
                      refine ⟨2695683063509373273156505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3594244084679164364208673 2695683063509373273156505)
                      ·
                        rfl

theorem cell23_5249824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_5249824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5249824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5249824 prefixEnd_5249824 := by exact prefixLift 5249824
  have htrace : WordTrace (prefixWord ++ tailWord_5249824) baseStart_5249824 baseEnd_5249824 := by
    simpa [prefixWord, tailWord_5249824, baseEnd_5249824] using wordTrace_append hprefix tailTrace_5249824
  have hstable : (prefixWord ++ tailWord_5249824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5249824).length < 2 ^ (prefixWord ++ tailWord_5249824).sum := by decide
  have hdescent : baseEnd_5249824 < baseStart_5249824 := by decide
  rcases family_descends (prefixWord ++ tailWord_5249824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5249907 : List Nat := [1, 1, 1, 2, 2, 1, 5, 2, 4, 4]
def baseStart_5249907 : Nat := 118140960795 + 5249907 * 2 ^ 59
def prefixEnd_5249907 : Nat := 4983230072969 + 3 ^ 40 * 5249907 * 2
def baseEnd_5249907 : Nat := 898575227467898816139541

theorem tailTrace_5249907 : CollatzResearch.WordTrace tailWord_5249907 prefixEnd_5249907 898575227467898816139541 := by
  unfold tailWord_5249907
  simp only [CollatzResearch.WordTrace]
  refine ⟨191479838991491026577723975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127653225994327351051815983 191479838991491026577723975)
  ·
    refine ⟨287219758487236539866585963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191479838991491026577723975 287219758487236539866585963)
    ·
      refine ⟨430829637730854809799878945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287219758487236539866585963 430829637730854809799878945)
      ·
        refine ⟨323122228298141107349909209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 430829637730854809799878945 323122228298141107349909209)
        ·
          refine ⟨242341671223605830512431907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 323122228298141107349909209 242341671223605830512431907)
          ·
            refine ⟨363512506835408745768647861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242341671223605830512431907 363512506835408745768647861)
            ·
              refine ⟨34079297515819569915810737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 363512506835408745768647861 34079297515819569915810737)
              ·
                refine ⟨25559473136864677436858053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34079297515819569915810737 25559473136864677436858053)
                ·
                  refine ⟨4792401213162127019410885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25559473136864677436858053 4792401213162127019410885)
                  ·
                    refine ⟨898575227467898816139541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4792401213162127019410885 898575227467898816139541)
                    ·
                      rfl

theorem cell23_5249907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 4, 4].length) (baseStart_5249907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5249907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5249907 prefixEnd_5249907 := by exact prefixLift 5249907
  have htrace : WordTrace (prefixWord ++ tailWord_5249907) baseStart_5249907 baseEnd_5249907 := by
    simpa [prefixWord, tailWord_5249907, baseEnd_5249907] using wordTrace_append hprefix tailTrace_5249907
  have hstable : (prefixWord ++ tailWord_5249907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5249907).length < 2 ^ (prefixWord ++ tailWord_5249907).sum := by decide
  have hdescent : baseEnd_5249907 < baseStart_5249907 := by decide
  rcases family_descends (prefixWord ++ tailWord_5249907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5249917 : List Nat := [1, 4, 1, 1, 2, 1, 3, 3, 1, 1, 5]
def baseStart_5249917 : Nat := 118140960795 + 5249917 * 2 ^ 59
def prefixEnd_5249917 : Nat := 4983230072969 + 3 ^ 40 * 5249917 * 2
def baseEnd_5249917 : Nat := 2695730817210241409293577

theorem tailTrace_5249917 : CollatzResearch.WordTrace tailWord_5249917 prefixEnd_5249917 2695730817210241409293577 := by
  unfold tailWord_5249917
  simp only [CollatzResearch.WordTrace]
  refine ⟨191480203721454798285588005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127653469147636532190392003 191480203721454798285588005)
  ·
    refine ⟨35902538197772774678547751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 191480203721454798285588005 35902538197772774678547751)
    ·
      refine ⟨53853807296659162017821627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35902538197772774678547751 53853807296659162017821627)
      ·
        refine ⟨80780710944988743026732441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53853807296659162017821627 80780710944988743026732441)
        ·
          refine ⟨60585533208741557270049331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80780710944988743026732441 60585533208741557270049331)
          ·
            refine ⟨90878299813112335905073997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60585533208741557270049331 90878299813112335905073997)
            ·
              refine ⟨34079362429917125964402749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90878299813112335905073997 34079362429917125964402749)
              ·
                refine ⟨12779760911218922236651031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34079362429917125964402749 12779760911218922236651031)
                ·
                  refine ⟨19169641366828383354976547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12779760911218922236651031 19169641366828383354976547)
                  ·
                    refine ⟨28754462050242575032464821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19169641366828383354976547 28754462050242575032464821)
                    ·
                      refine ⟨2695730817210241409293577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28754462050242575032464821 2695730817210241409293577)
                      ·
                        rfl

theorem cell23_5249917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 3, 1, 1, 5].length) (baseStart_5249917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5249917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5249917 prefixEnd_5249917 := by exact prefixLift 5249917
  have htrace : WordTrace (prefixWord ++ tailWord_5249917) baseStart_5249917 baseEnd_5249917 := by
    simpa [prefixWord, tailWord_5249917, baseEnd_5249917] using wordTrace_append hprefix tailTrace_5249917
  have hstable : (prefixWord ++ tailWord_5249917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5249917).length < 2 ^ (prefixWord ++ tailWord_5249917).sum := by decide
  have hdescent : baseEnd_5249917 < baseStart_5249917 := by decide
  rcases family_descends (prefixWord ++ tailWord_5249917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5249924 : List Nat := [2, 3, 2, 1, 1, 1, 1, 6, 2, 4]
def baseStart_5249924 : Nat := 118140960795 + 5249924 * 2 ^ 59
def prefixEnd_5249924 : Nat := 4983230072969 + 3 ^ 40 * 5249924 * 2
def baseEnd_5249924 : Nat := 898578137191607627302015

theorem tailTrace_5249924 : CollatzResearch.WordTrace tailWord_5249924 prefixEnd_5249924 898578137191607627302015 := by
  unfold tailWord_5249924
  simp only [CollatzResearch.WordTrace]
  refine ⟨95740229516214719240546413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127653639354952958987395217 95740229516214719240546413)
  ·
    refine ⟨35902586068580519715204905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95740229516214719240546413 35902586068580519715204905)
    ·
      refine ⟨26926939551435389786403679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35902586068580519715204905 26926939551435389786403679)
      ·
        refine ⟨40390409327153084679605519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26926939551435389786403679 40390409327153084679605519)
        ·
          refine ⟨60585613990729627019408279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40390409327153084679605519 60585613990729627019408279)
          ·
            refine ⟨90878420986094440529112419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60585613990729627019408279 90878420986094440529112419)
            ·
              refine ⟨136317631479141660793668629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90878420986094440529112419 136317631479141660793668629)
              ·
                refine ⟨6389888975584765349703217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 136317631479141660793668629 6389888975584765349703217)
                ·
                  refine ⟨4792416731688574012277413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6389888975584765349703217 4792416731688574012277413)
                  ·
                    refine ⟨898578137191607627302015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4792416731688574012277413 898578137191607627302015)
                    ·
                      rfl

theorem cell23_5249924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_5249924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5249924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5249924 prefixEnd_5249924 := by exact prefixLift 5249924
  have htrace : WordTrace (prefixWord ++ tailWord_5249924) baseStart_5249924 baseEnd_5249924 := by
    simpa [prefixWord, tailWord_5249924, baseEnd_5249924] using wordTrace_append hprefix tailTrace_5249924
  have hstable : (prefixWord ++ tailWord_5249924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5249924).length < 2 ^ (prefixWord ++ tailWord_5249924).sum := by decide
  have hdescent : baseEnd_5249924 < baseStart_5249924 := by decide
  rcases family_descends (prefixWord ++ tailWord_5249924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
