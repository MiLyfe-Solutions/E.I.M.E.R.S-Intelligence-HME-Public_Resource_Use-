import V185TrunkScan23Chunk0133

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_793682 : List Nat := [3, 2, 2, 1, 3, 1, 1, 3, 2, 2, 3]
def baseStart_793682 : Nat := 118140960795 + 793682 * 2 ^ 59
def prefixEnd_793682 : Nat := 4983230072969 + 3 ^ 40 * 793682 * 2
def baseEnd_793682 : Nat := 407540352821868949224929

theorem tailTrace_793682 : CollatzResearch.WordTrace tailWord_793682 prefixEnd_793682 407540352821868949224929 := by
  unfold tailWord_793682
  simp only [CollatzResearch.WordTrace]
  refine ⟨7236990177658284734753825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19298640473755425959343533 7236990177658284734753825)
  ·
    refine ⟨5427742633243713551065369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7236990177658284734753825 5427742633243713551065369)
    ·
      refine ⟨4070806974932785163299027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5427742633243713551065369 4070806974932785163299027)
      ·
        refine ⟨6106210462399177744948541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4070806974932785163299027 6106210462399177744948541)
        ·
          refine ⟨2289828923399691654355703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6106210462399177744948541 2289828923399691654355703)
          ·
            refine ⟨3434743385099537481533555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2289828923399691654355703 3434743385099537481533555)
            ·
              refine ⟨5152115077649306222300333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3434743385099537481533555 5152115077649306222300333)
              ·
                refine ⟨1932043154118489833362625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5152115077649306222300333 1932043154118489833362625)
                ·
                  refine ⟨1449032365588867375021969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1932043154118489833362625 1449032365588867375021969)
                  ·
                    refine ⟨1086774274191650531266477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1449032365588867375021969 1086774274191650531266477)
                    ·
                      refine ⟨407540352821868949224929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1086774274191650531266477 407540352821868949224929)
                      ·
                        rfl

theorem cell23_793682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_793682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_793682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_793682 prefixEnd_793682 := by exact prefixLift 793682
  have htrace : WordTrace (prefixWord ++ tailWord_793682) baseStart_793682 baseEnd_793682 := by
    simpa [prefixWord, tailWord_793682, baseEnd_793682] using wordTrace_append hprefix tailTrace_793682
  have hstable : (prefixWord ++ tailWord_793682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793682).length < 2 ^ (prefixWord ++ tailWord_793682).sum := by decide
  have hdescent : baseEnd_793682 < baseStart_793682 := by decide
  rcases family_descends (prefixWord ++ tailWord_793682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793706 : List Nat := [3, 1, 3, 2, 2, 1, 4, 2, 1, 4]
def baseStart_793706 : Nat := 118140960795 + 793706 * 2 ^ 59
def prefixEnd_793706 : Nat := 4983230072969 + 3 ^ 40 * 793706 * 2
def baseEnd_793706 : Nat := 135850892119192285108273

theorem tailTrace_793706 : CollatzResearch.WordTrace tailWord_793706 prefixEnd_793706 135850892119192285108273 := by
  unfold tailWord_793706
  simp only [CollatzResearch.WordTrace]
  refine ⟨7237209015636547759472243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19299224041697460691925981 7237209015636547759472243)
  ·
    refine ⟨10855813523454821639208365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7237209015636547759472243 10855813523454821639208365)
    ·
      refine ⟨4070930071295558114703137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10855813523454821639208365 4070930071295558114703137)
      ·
        refine ⟨3053197553471668586027353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4070930071295558114703137 3053197553471668586027353)
        ·
          refine ⟨2289898165103751439520515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3053197553471668586027353 2289898165103751439520515)
          ·
            refine ⟨3434847247655627159280773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2289898165103751439520515 3434847247655627159280773)
            ·
              refine ⟨644033858935430092365145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3434847247655627159280773 644033858935430092365145)
              ·
                refine ⟨483025394201572569273859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 644033858935430092365145 483025394201572569273859)
                ·
                  refine ⟨724538091302358853910789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 483025394201572569273859 724538091302358853910789)
                  ·
                    refine ⟨135850892119192285108273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 724538091302358853910789 135850892119192285108273)
                    ·
                      rfl

theorem cell23_793706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 4, 2, 1, 4].length) (baseStart_793706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_793706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_793706 prefixEnd_793706 := by exact prefixLift 793706
  have htrace : WordTrace (prefixWord ++ tailWord_793706) baseStart_793706 baseEnd_793706 := by
    simpa [prefixWord, tailWord_793706, baseEnd_793706] using wordTrace_append hprefix tailTrace_793706
  have hstable : (prefixWord ++ tailWord_793706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793706).length < 2 ^ (prefixWord ++ tailWord_793706).sum := by decide
  have hdescent : baseEnd_793706 < baseStart_793706 := by decide
  rcases family_descends (prefixWord ++ tailWord_793706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793712 : List Nat := [2, 1, 1, 1, 5, 1, 2, 3, 3, 1, 3]
def baseStart_793712 : Nat := 118140960795 + 793712 * 2 ^ 59
def prefixEnd_793712 : Nat := 4983230072969 + 3 ^ 40 * 793712 * 2
def baseEnd_793712 : Nat := 407555757241503831849791

theorem tailTrace_793712 : CollatzResearch.WordTrace tailWord_793712 prefixEnd_793712 407555757241503831849791 := by
  unfold tailWord_793712
  simp only [CollatzResearch.WordTrace]
  refine ⟨14474527450262227031303695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19299369933682969375071593 14474527450262227031303695)
  ·
    refine ⟨21711791175393340546955543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14474527450262227031303695 21711791175393340546955543)
    ·
      refine ⟨32567686763090010820433315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21711791175393340546955543 32567686763090010820433315)
      ·
        refine ⟨48851530144635016230649973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32567686763090010820433315 48851530144635016230649973)
        ·
          refine ⟨4579830951059532771623435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48851530144635016230649973 4579830951059532771623435)
          ·
            refine ⟨6869746426589299157435153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4579830951059532771623435 6869746426589299157435153)
            ·
              refine ⟨5152309819941974368076365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6869746426589299157435153 5152309819941974368076365)
              ·
                refine ⟨1932116182478240388028637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5152309819941974368076365 1932116182478240388028637)
                ·
                  refine ⟨724543568429340145510739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1932116182478240388028637 724543568429340145510739)
                  ·
                    refine ⟨1086815352644010218266109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 724543568429340145510739 1086815352644010218266109)
                    ·
                      refine ⟨407555757241503831849791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1086815352644010218266109 407555757241503831849791)
                      ·
                        rfl

theorem cell23_793712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 3, 3, 1, 3].length) (baseStart_793712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_793712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_793712 prefixEnd_793712 := by exact prefixLift 793712
  have htrace : WordTrace (prefixWord ++ tailWord_793712) baseStart_793712 baseEnd_793712 := by
    simpa [prefixWord, tailWord_793712, baseEnd_793712] using wordTrace_append hprefix tailTrace_793712
  have hstable : (prefixWord ++ tailWord_793712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793712).length < 2 ^ (prefixWord ++ tailWord_793712).sum := by decide
  have hdescent : baseEnd_793712 < baseStart_793712 := by decide
  rcases family_descends (prefixWord ++ tailWord_793712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793729 : List Nat := [1, 2, 4, 2, 2, 2, 1, 2, 3, 1, 3]
def baseStart_793729 : Nat := 118140960795 + 793729 * 2 ^ 59
def prefixEnd_793729 : Nat := 4983230072969 + 3 ^ 40 * 793729 * 2
def baseEnd_793729 : Nat := 407564486412630265337213

theorem tailTrace_793729 : CollatzResearch.WordTrace tailWord_793729 prefixEnd_793729 407564486412630265337213 := by
  unfold tailWord_793729
  simp only [CollatzResearch.WordTrace]
  refine ⟨28949674941462865965976241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19299783294308577310650827 28949674941462865965976241)
  ·
    refine ⟨21712256206097149474482181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28949674941462865965976241 21712256206097149474482181)
    ·
      refine ⟨4071048038643215526465409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21712256206097149474482181 4071048038643215526465409)
      ·
        refine ⟨3053286028982411644849057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4071048038643215526465409 3053286028982411644849057)
        ·
          refine ⟨2289964521736808733636793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3053286028982411644849057 2289964521736808733636793)
          ·
            refine ⟨1717473391302606550227595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2289964521736808733636793 1717473391302606550227595)
            ·
              refine ⟨2576210086953909825341393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1717473391302606550227595 2576210086953909825341393)
              ·
                refine ⟨1932157565215432369006045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2576210086953909825341393 1932157565215432369006045)
                ·
                  refine ⟨724559086955787138377267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1932157565215432369006045 724559086955787138377267)
                  ·
                    refine ⟨1086838630433680707565901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 724559086955787138377267 1086838630433680707565901)
                    ·
                      refine ⟨407564486412630265337213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1086838630433680707565901 407564486412630265337213)
                      ·
                        rfl

theorem cell23_793729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_793729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_793729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_793729 prefixEnd_793729 := by exact prefixLift 793729
  have htrace : WordTrace (prefixWord ++ tailWord_793729) baseStart_793729 baseEnd_793729 := by
    simpa [prefixWord, tailWord_793729, baseEnd_793729] using wordTrace_append hprefix tailTrace_793729
  have hstable : (prefixWord ++ tailWord_793729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793729).length < 2 ^ (prefixWord ++ tailWord_793729).sum := by decide
  have hdescent : baseEnd_793729 < baseStart_793729 := by decide
  rcases family_descends (prefixWord ++ tailWord_793729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793746 : List Nat := [3, 2, 3, 1, 1, 2, 1, 5, 1, 1, 3]
def baseStart_793746 : Nat := 118140960795 + 793746 * 2 ^ 59
def prefixEnd_793746 : Nat := 4983230072969 + 3 ^ 40 * 793746 * 2
def baseEnd_793746 : Nat := 407573215583756698824635

theorem tailTrace_793746 : CollatzResearch.WordTrace tailWord_793746 prefixEnd_793746 407573215583756698824635 := by
  unfold tailWord_793746
  simp only [CollatzResearch.WordTrace]
  refine ⟨7237573745600319467336273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19300196654934185246230061 7237573745600319467336273)
  ·
    refine ⟨5428180309200239600502205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7237573745600319467336273 5428180309200239600502205)
    ·
      refine ⟨2035567615950089850188327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5428180309200239600502205 2035567615950089850188327)
      ·
        refine ⟨3053351423925134775282491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2035567615950089850188327 3053351423925134775282491)
        ·
          refine ⟨4580027135887702162923737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3053351423925134775282491 4580027135887702162923737)
          ·
            refine ⟨3435020351915776622192803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4580027135887702162923737 3435020351915776622192803)
            ·
              refine ⟨5152530527873664933289205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3435020351915776622192803 5152530527873664933289205)
              ·
                refine ⟨483049736988156087495863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5152530527873664933289205 483049736988156087495863)
                ·
                  refine ⟨724574605482234131243795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 483049736988156087495863 724574605482234131243795)
                  ·
                    refine ⟨1086861908223351196865693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 724574605482234131243795 1086861908223351196865693)
                    ·
                      refine ⟨407573215583756698824635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1086861908223351196865693 407573215583756698824635)
                      ·
                        rfl

theorem cell23_793746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 5, 1, 1, 3].length) (baseStart_793746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_793746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_793746 prefixEnd_793746 := by exact prefixLift 793746
  have htrace : WordTrace (prefixWord ++ tailWord_793746) baseStart_793746 baseEnd_793746 := by
    simpa [prefixWord, tailWord_793746, baseEnd_793746] using wordTrace_append hprefix tailTrace_793746
  have hstable : (prefixWord ++ tailWord_793746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793746).length < 2 ^ (prefixWord ++ tailWord_793746).sum := by decide
  have hdescent : baseEnd_793746 < baseStart_793746 := by decide
  rcases family_descends (prefixWord ++ tailWord_793746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793755 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 7, 2, 3]
def baseStart_793755 : Nat := 118140960795 + 793755 * 2 ^ 59
def prefixEnd_793755 : Nat := 4983230072969 + 3 ^ 40 * 793755 * 2
def baseEnd_793755 : Nat := 407577836909647163612093

theorem tailTrace_793755 : CollatzResearch.WordTrace tailWord_793755 prefixEnd_793755 407577836909647163612093 := by
  unfold tailWord_793755
  simp only [CollatzResearch.WordTrace]
  refine ⟨28950623239368672406422719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19300415492912448270948479 28950623239368672406422719)
  ·
    refine ⟨43425934859053008609634079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28950623239368672406422719 43425934859053008609634079)
    ·
      refine ⟨65138902288579512914451119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43425934859053008609634079 65138902288579512914451119)
      ·
        refine ⟨97708353432869269371676679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65138902288579512914451119 97708353432869269371676679)
        ·
          refine ⟨146562530149303904057515019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97708353432869269371676679 146562530149303904057515019)
          ·
            refine ⟨219843795223955856086272529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146562530149303904057515019 219843795223955856086272529)
            ·
              refine ⟨164882846417966892064704397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 219843795223955856086272529 164882846417966892064704397)
              ·
                refine ⟨61831067406737584524264149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 164882846417966892064704397 61831067406737584524264149)
                ·
                  refine ⟨1449165642345412137287441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 61831067406737584524264149 1449165642345412137287441)
                  ·
                    refine ⟨1086874231759059102965581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1449165642345412137287441 1086874231759059102965581)
                    ·
                      refine ⟨407577836909647163612093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1086874231759059102965581 407577836909647163612093)
                      ·
                        rfl

theorem cell23_793755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 7, 2, 3].length) (baseStart_793755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_793755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_793755 prefixEnd_793755 := by exact prefixLift 793755
  have htrace : WordTrace (prefixWord ++ tailWord_793755) baseStart_793755 baseEnd_793755 := by
    simpa [prefixWord, tailWord_793755, baseEnd_793755] using wordTrace_append hprefix tailTrace_793755
  have hstable : (prefixWord ++ tailWord_793755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793755).length < 2 ^ (prefixWord ++ tailWord_793755).sum := by decide
  have hdescent : baseEnd_793755 < baseStart_793755 := by decide
  rcases family_descends (prefixWord ++ tailWord_793755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793836 : List Nat := [2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 3]
def baseStart_793836 : Nat := 118140960795 + 793836 * 2 ^ 59
def prefixEnd_793836 : Nat := 4983230072969 + 3 ^ 40 * 793836 * 2
def baseEnd_793836 : Nat := 407619428842661346699221

theorem tailTrace_793836 : CollatzResearch.WordTrace tailWord_793836 prefixEnd_793836 407619428842661346699221 := by
  unfold tailWord_793836
  simp only [CollatzResearch.WordTrace]
  refine ⟨14476788776037611620060681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19302385034716815493414241 14476788776037611620060681)
  ·
    refine ⟨10857591582028208715045511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14476788776037611620060681 10857591582028208715045511)
    ·
      refine ⟨16286387373042313072568267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10857591582028208715045511 16286387373042313072568267)
      ·
        refine ⟨24429581059563469608852401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16286387373042313072568267 24429581059563469608852401)
        ·
          refine ⟨18322185794672602206639301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24429581059563469608852401 18322185794672602206639301)
          ·
            refine ⟨3435409836501112913744869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18322185794672602206639301 3435409836501112913744869)
            ·
              refine ⟨644139344343958671327163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3435409836501112913744869 644139344343958671327163)
              ·
                refine ⟨966209016515938006990745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 644139344343958671327163 966209016515938006990745)
                ·
                  refine ⟨724656762386953505243059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 966209016515938006990745 724656762386953505243059)
                  ·
                    refine ⟨1086985143580430257864589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 724656762386953505243059 1086985143580430257864589)
                    ·
                      refine ⟨407619428842661346699221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1086985143580430257864589 407619428842661346699221)
                      ·
                        rfl

theorem cell23_793836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 3].length) (baseStart_793836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_793836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_793836 prefixEnd_793836 := by exact prefixLift 793836
  have htrace : WordTrace (prefixWord ++ tailWord_793836) baseStart_793836 baseEnd_793836 := by
    simpa [prefixWord, tailWord_793836, baseEnd_793836] using wordTrace_append hprefix tailTrace_793836
  have hstable : (prefixWord ++ tailWord_793836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793836).length < 2 ^ (prefixWord ++ tailWord_793836).sum := by decide
  have hdescent : baseEnd_793836 < baseStart_793836 := by decide
  rcases family_descends (prefixWord ++ tailWord_793836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793859 : List Nat := [1, 1, 1, 3, 2, 5, 1, 2, 1, 4, 2]
def baseStart_793859 : Nat := 118140960795 + 793859 * 2 ^ 59
def prefixEnd_793859 : Nat := 4983230072969 + 3 ^ 40 * 793859 * 2
def baseEnd_793859 : Nat := 407631238897714756711615

theorem tailTrace_793859 : CollatzResearch.WordTrace tailWord_793859 prefixEnd_793859 407631238897714756711615 := by
  unfold tailWord_793859
  simp only [CollatzResearch.WordTrace]
  refine ⟨28954416430991898168208631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19302944287327932112139087 28954416430991898168208631)
  ·
    refine ⟨43431624646487847252312947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28954416430991898168208631 43431624646487847252312947)
    ·
      refine ⟨65147436969731770878469421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43431624646487847252312947 65147436969731770878469421)
      ·
        refine ⟨24430288863649414079426033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65147436969731770878469421 24430288863649414079426033)
        ·
          refine ⟨18322716647737060559569525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24430288863649414079426033 18322716647737060559569525)
          ·
            refine ⟨1717754685725349427459643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18322716647737060559569525 1717754685725349427459643)
            ·
              refine ⟨2576632028588024141189465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1717754685725349427459643 2576632028588024141189465)
              ·
                refine ⟨1932474021441018105892099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2576632028588024141189465 1932474021441018105892099)
                ·
                  refine ⟨2898711032161527158838149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1932474021441018105892099 2898711032161527158838149)
                  ·
                    refine ⟨543508318530286342282153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2898711032161527158838149 543508318530286342282153)
                    ·
                      refine ⟨407631238897714756711615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 543508318530286342282153 407631238897714756711615)
                      ·
                        rfl

theorem cell23_793859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 2, 1, 4, 2].length) (baseStart_793859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_793859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_793859 prefixEnd_793859 := by exact prefixLift 793859
  have htrace : WordTrace (prefixWord ++ tailWord_793859) baseStart_793859 baseEnd_793859 := by
    simpa [prefixWord, tailWord_793859, baseEnd_793859] using wordTrace_append hprefix tailTrace_793859
  have hstable : (prefixWord ++ tailWord_793859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793859).length < 2 ^ (prefixWord ++ tailWord_793859).sum := by decide
  have hdescent : baseEnd_793859 < baseStart_793859 := by decide
  rcases family_descends (prefixWord ++ tailWord_793859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793886 : List Nat := [4, 3, 2, 1, 2, 1, 1, 1, 2, 6]
def baseStart_793886 : Nat := 118140960795 + 793886 * 2 ^ 59
def prefixEnd_793886 : Nat := 4983230072969 + 3 ^ 40 * 793886 * 2
def baseEnd_793886 : Nat := 135881700958462050357997

theorem tailTrace_793886 : CollatzResearch.WordTrace tailWord_793886 prefixEnd_793886 135881700958462050357997 := by
  unfold tailWord_793886
  simp only [CollatzResearch.WordTrace]
  refine ⟨3619425150236760222430189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19303600801262721186294341 3619425150236760222430189)
  ·
    refine ⟨1357284431338785083411321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3619425150236760222430189 1357284431338785083411321)
    ·
      refine ⟨1017963323504088812558491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1357284431338785083411321 1017963323504088812558491)
      ·
        refine ⟨1526944985256133218837737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1017963323504088812558491 1526944985256133218837737)
        ·
          refine ⟨1145208738942099914128303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1526944985256133218837737 1145208738942099914128303)
          ·
            refine ⟨1717813108413149871192455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1145208738942099914128303 1717813108413149871192455)
            ·
              refine ⟨2576719662619724806788683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1717813108413149871192455 2576719662619724806788683)
              ·
                refine ⟨3865079493929587210183025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2576719662619724806788683 3865079493929587210183025)
                ·
                  refine ⟨2898809620447190407637269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3865079493929587210183025 2898809620447190407637269)
                  ·
                    refine ⟨135881700958462050357997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2898809620447190407637269 135881700958462050357997)
                    ·
                      rfl

theorem cell23_793886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_793886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_793886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_793886 prefixEnd_793886 := by exact prefixLift 793886
  have htrace : WordTrace (prefixWord ++ tailWord_793886) baseStart_793886 baseEnd_793886 := by
    simpa [prefixWord, tailWord_793886, baseEnd_793886] using wordTrace_append hprefix tailTrace_793886
  have hstable : (prefixWord ++ tailWord_793886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793886).length < 2 ^ (prefixWord ++ tailWord_793886).sum := by decide
  have hdescent : baseEnd_793886 < baseStart_793886 := by decide
  rcases family_descends (prefixWord ++ tailWord_793886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793925 : List Nat := [1, 3, 1, 1, 1, 2, 1, 2, 1, 10]
def baseStart_793925 : Nat := 118140960795 + 793925 * 2 ^ 59
def prefixEnd_793925 : Nat := 4983230072969 + 3 ^ 40 * 793925 * 2
def baseEnd_793925 : Nat := 135888376206970499495437

theorem tailTrace_793925 : CollatzResearch.WordTrace tailWord_793925 prefixEnd_793925 135888376206970499495437 := by
  unfold tailWord_793925
  simp only [CollatzResearch.WordTrace]
  refine ⟨28956823648752791440111229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19304549099168527626740819 28956823648752791440111229)
  ·
    refine ⟨10858808868282296790041711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28956823648752791440111229 10858808868282296790041711)
    ·
      refine ⟨16288213302423445185062567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10858808868282296790041711 16288213302423445185062567)
      ·
        refine ⟨24432319953635167777593851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16288213302423445185062567 24432319953635167777593851)
        ·
          refine ⟨36648479930452751666390777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24432319953635167777593851 36648479930452751666390777)
          ·
            refine ⟨27486359947839563749793083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36648479930452751666390777 27486359947839563749793083)
            ·
              refine ⟨41229539921759345624689625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27486359947839563749793083 41229539921759345624689625)
              ·
                refine ⟨30922154941319509218517219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41229539921759345624689625 30922154941319509218517219)
                ·
                  refine ⟨46383232411979263827775829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30922154941319509218517219 46383232411979263827775829)
                  ·
                    refine ⟨135888376206970499495437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 46383232411979263827775829 135888376206970499495437)
                    ·
                      rfl

theorem cell23_793925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 10].length) (baseStart_793925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_793925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_793925 prefixEnd_793925 := by exact prefixLift 793925
  have htrace : WordTrace (prefixWord ++ tailWord_793925) baseStart_793925 baseEnd_793925 := by
    simpa [prefixWord, tailWord_793925, baseEnd_793925] using wordTrace_append hprefix tailTrace_793925
  have hstable : (prefixWord ++ tailWord_793925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793925).length < 2 ^ (prefixWord ++ tailWord_793925).sum := by decide
  have hdescent : baseEnd_793925 < baseStart_793925 := by decide
  rcases family_descends (prefixWord ++ tailWord_793925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793993 : List Nat := [1, 2, 1, 1, 8, 1, 1, 1, 3, 4]
def baseStart_793993 : Nat := 118140960795 + 793993 * 2 ^ 59
def prefixEnd_793993 : Nat := 4983230072969 + 3 ^ 40 * 793993 * 2
def baseEnd_793993 : Nat := 135900015101805744145333

theorem tailTrace_793993 : CollatzResearch.WordTrace tailWord_793993 prefixEnd_793993 135900015101805744145333 := by
  unfold tailWord_793993
  simp only [CollatzResearch.WordTrace]
  refine ⟨28959303812506439053586633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19306202541670959369057755 28959303812506439053586633)
  ·
    refine ⟨21719477859379829290189975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28959303812506439053586633 21719477859379829290189975)
    ·
      refine ⟨32579216789069743935284963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21719477859379829290189975 32579216789069743935284963)
      ·
        refine ⟨48868825183604615902927445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32579216789069743935284963 48868825183604615902927445)
        ·
          refine ⟨572681545120366592612431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 48868825183604615902927445 572681545120366592612431)
          ·
            refine ⟨859022317680549888918647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 572681545120366592612431 859022317680549888918647)
            ·
              refine ⟨1288533476520824833377971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 859022317680549888918647 1288533476520824833377971)
              ·
                refine ⟨1932800214781237250066957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1288533476520824833377971 1932800214781237250066957)
                ·
                  refine ⟨724800080542963968775109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1932800214781237250066957 724800080542963968775109)
                  ·
                    refine ⟨135900015101805744145333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 724800080542963968775109 135900015101805744145333)
                    ·
                      rfl

theorem cell23_793993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 1, 3, 4].length) (baseStart_793993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_793993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_793993 prefixEnd_793993 := by exact prefixLift 793993
  have htrace : WordTrace (prefixWord ++ tailWord_793993) baseStart_793993 baseEnd_793993 := by
    simpa [prefixWord, tailWord_793993, baseEnd_793993] using wordTrace_append hprefix tailTrace_793993
  have hstable : (prefixWord ++ tailWord_793993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793993).length < 2 ^ (prefixWord ++ tailWord_793993).sum := by decide
  have hdescent : baseEnd_793993 < baseStart_793993 := by decide
  rcases family_descends (prefixWord ++ tailWord_793993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794033 : List Nat := [1, 2, 2, 4, 1, 1, 2, 5, 1, 1, 3]
def baseStart_794033 : Nat := 118140960795 + 794033 * 2 ^ 59
def prefixEnd_794033 : Nat := 4983230072969 + 3 ^ 40 * 794033 * 2
def baseEnd_794033 : Nat := 407720584531597075935815

theorem tailTrace_794033 : CollatzResearch.WordTrace tailWord_794033 prefixEnd_794033 407720584531597075935815 := by
  unfold tailWord_794033
  simp only [CollatzResearch.WordTrace]
  refine ⟨28960762732361525885042753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19307175154907683923361835 28960762732361525885042753)
  ·
    refine ⟨21720572049271144413782065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28960762732361525885042753 21720572049271144413782065)
    ·
      refine ⟨16290429036953358310336549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21720572049271144413782065 16290429036953358310336549)
      ·
        refine ⟨3054455444428754683188103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16290429036953358310336549 3054455444428754683188103)
        ·
          refine ⟨4581683166643132024782155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3054455444428754683188103 4581683166643132024782155)
          ·
            refine ⟨6872524749964698037173233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4581683166643132024782155 6872524749964698037173233)
            ·
              refine ⟨5154393562473523527879925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6872524749964698037173233 5154393562473523527879925)
              ·
                refine ⟨483224396481892830738743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5154393562473523527879925 483224396481892830738743)
                ·
                  refine ⟨724836594722839246108115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 483224396481892830738743 724836594722839246108115)
                  ·
                    refine ⟨1087254892084258869162173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 724836594722839246108115 1087254892084258869162173)
                    ·
                      refine ⟨407720584531597075935815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1087254892084258869162173 407720584531597075935815)
                      ·
                        rfl

theorem cell23_794033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 5, 1, 1, 3].length) (baseStart_794033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794033 prefixEnd_794033 := by exact prefixLift 794033
  have htrace : WordTrace (prefixWord ++ tailWord_794033) baseStart_794033 baseEnd_794033 := by
    simpa [prefixWord, tailWord_794033, baseEnd_794033] using wordTrace_append hprefix tailTrace_794033
  have hstable : (prefixWord ++ tailWord_794033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794033).length < 2 ^ (prefixWord ++ tailWord_794033).sum := by decide
  have hdescent : baseEnd_794033 < baseStart_794033 := by decide
  rcases family_descends (prefixWord ++ tailWord_794033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794059 : List Nat := [1, 1, 1, 1, 3, 3, 3, 2, 3, 2, 3]
def baseStart_794059 : Nat := 118140960795 + 794059 * 2 ^ 59
def prefixEnd_794059 : Nat := 4983230072969 + 3 ^ 40 * 794059 * 2
def baseEnd_794059 : Nat := 407733935028613974210695

theorem tailTrace_794059 : CollatzResearch.WordTrace tailWord_794059 prefixEnd_794059 407733935028613974210695 := by
  unfold tailWord_794059
  simp only [CollatzResearch.WordTrace]
  refine ⟨28961711030267332325489231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19307807353511554883659487 28961711030267332325489231)
  ·
    refine ⟨43442566545400998488233847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28961711030267332325489231 43442566545400998488233847)
    ·
      refine ⟨65163849818101497732350771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43442566545400998488233847 65163849818101497732350771)
      ·
        refine ⟨97745774727152246598526157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65163849818101497732350771 97745774727152246598526157)
        ·
          refine ⟨36654665522682092474447309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97745774727152246598526157 36654665522682092474447309)
          ·
            refine ⟨13745499571005784677917741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36654665522682092474447309 13745499571005784677917741)
            ·
              refine ⟨5154562339127169254219153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13745499571005784677917741 5154562339127169254219153)
              ·
                refine ⟨3865921754345376940664365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5154562339127169254219153 3865921754345376940664365)
                ·
                  refine ⟨1449720657879516352749137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3865921754345376940664365 1449720657879516352749137)
                  ·
                    refine ⟨1087290493409637264561853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1449720657879516352749137 1087290493409637264561853)
                    ·
                      refine ⟨407733935028613974210695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1087290493409637264561853 407733935028613974210695)
                      ·
                        rfl

theorem cell23_794059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 3, 2, 3].length) (baseStart_794059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794059 prefixEnd_794059 := by exact prefixLift 794059
  have htrace : WordTrace (prefixWord ++ tailWord_794059) baseStart_794059 baseEnd_794059 := by
    simpa [prefixWord, tailWord_794059, baseEnd_794059] using wordTrace_append hprefix tailTrace_794059
  have hstable : (prefixWord ++ tailWord_794059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794059).length < 2 ^ (prefixWord ++ tailWord_794059).sum := by decide
  have hdescent : baseEnd_794059 < baseStart_794059 := by decide
  rcases family_descends (prefixWord ++ tailWord_794059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794073 : List Nat := [1, 2, 1, 2, 4, 3, 1, 2, 3, 2, 2]
def baseStart_794073 : Nat := 118140960795 + 794073 * 2 ^ 59
def prefixEnd_794073 : Nat := 4983230072969 + 3 ^ 40 * 794073 * 2
def baseEnd_794073 : Nat := 407741123757776919435631

theorem tailTrace_794073 : CollatzResearch.WordTrace tailWord_794073 prefixEnd_794073 407741123757776919435631 := by
  unfold tailWord_794073
  simp only [CollatzResearch.WordTrace]
  refine ⟨28962221652216612716498873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19308147768144408477665915 28962221652216612716498873)
  ·
    refine ⟨21721666239162459537374155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28962221652216612716498873 21721666239162459537374155)
    ·
      refine ⟨32582499358743689306061233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21721666239162459537374155 32582499358743689306061233)
      ·
        refine ⟨24436874519057766979545925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32582499358743689306061233 24436874519057766979545925)
        ·
          refine ⟨4581913972323331308664861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24436874519057766979545925 4581913972323331308664861)
          ·
            refine ⟨1718217739621249240749323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4581913972323331308664861 1718217739621249240749323)
            ·
              refine ⟨2577326609431873861123985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1718217739621249240749323 2577326609431873861123985)
              ·
                refine ⟨1932994957073905395842989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2577326609431873861123985 1932994957073905395842989)
                ·
                  refine ⟨724873108902714523441121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1932994957073905395842989 724873108902714523441121)
                  ·
                    refine ⟨543654831677035892580841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 724873108902714523441121 543654831677035892580841)
                    ·
                      refine ⟨407741123757776919435631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 543654831677035892580841 407741123757776919435631)
                      ·
                        rfl

theorem cell23_794073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 2, 3, 2, 2].length) (baseStart_794073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794073 prefixEnd_794073 := by exact prefixLift 794073
  have htrace : WordTrace (prefixWord ++ tailWord_794073) baseStart_794073 baseEnd_794073 := by
    simpa [prefixWord, tailWord_794073, baseEnd_794073] using wordTrace_append hprefix tailTrace_794073
  have hstable : (prefixWord ++ tailWord_794073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794073).length < 2 ^ (prefixWord ++ tailWord_794073).sum := by decide
  have hdescent : baseEnd_794073 < baseStart_794073 := by decide
  rcases family_descends (prefixWord ++ tailWord_794073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794079 : List Nat := [1, 1, 2, 3, 3, 1, 5, 7]
def baseStart_794079 : Nat := 118140960795 + 794079 * 2 ^ 59
def prefixEnd_794079 : Nat := 4983230072969 + 3 ^ 40 * 794079 * 2
def baseEnd_794079 : Nat := 15101637208951996146689

theorem tailTrace_794079 : CollatzResearch.WordTrace tailWord_794079 prefixEnd_794079 15101637208951996146689 := by
  unfold tailWord_794079
  simp only [CollatzResearch.WordTrace]
  refine ⟨28962440490194875741217291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19308293660129917160811527 28962440490194875741217291)
  ·
    refine ⟨43443660735292313611825937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28962440490194875741217291 43443660735292313611825937)
    ·
      refine ⟨32582745551469235208869453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43443660735292313611825937 32582745551469235208869453)
      ·
        refine ⟨12218529581800963203326045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32582745551469235208869453 12218529581800963203326045)
        ·
          refine ⟨4581948593175361201247267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12218529581800963203326045 4581948593175361201247267)
          ·
            refine ⟨6872922889763041801870901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4581948593175361201247267 6872922889763041801870901)
            ·
              refine ⟨644336520915285168925397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6872922889763041801870901 644336520915285168925397)
              ·
                refine ⟨15101637208951996146689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 644336520915285168925397 15101637208951996146689)
                ·
                  rfl

theorem cell23_794079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 5, 7].length) (baseStart_794079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794079 prefixEnd_794079 := by exact prefixLift 794079
  have htrace : WordTrace (prefixWord ++ tailWord_794079) baseStart_794079 baseEnd_794079 := by
    simpa [prefixWord, tailWord_794079, baseEnd_794079] using wordTrace_append hprefix tailTrace_794079
  have hstable : (prefixWord ++ tailWord_794079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794079).length < 2 ^ (prefixWord ++ tailWord_794079).sum := by decide
  have hdescent : baseEnd_794079 < baseStart_794079 := by decide
  rcases family_descends (prefixWord ++ tailWord_794079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794090 : List Nat := [3, 1, 3, 1, 4, 2, 2, 1, 1, 1, 4]
def baseStart_794090 : Nat := 118140960795 + 794090 * 2 ^ 59
def prefixEnd_794090 : Nat := 4983230072969 + 3 ^ 40 * 794090 * 2
def baseEnd_794090 : Nat := 407749852928903352923053

theorem tailTrace_794090 : CollatzResearch.WordTrace tailWord_794090 prefixEnd_794090 407749852928903352923053 := by
  unfold tailWord_794090
  simp only [CollatzResearch.WordTrace]
  refine ⟨7240710423288756154966931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19308561128770016413245149 7240710423288756154966931)
  ·
    refine ⟨10861065634933134232450397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7240710423288756154966931 10861065634933134232450397)
    ·
      refine ⟨4072899613099925337168899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10861065634933134232450397 4072899613099925337168899)
      ·
        refine ⟨6109349419649888005753349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4072899613099925337168899 6109349419649888005753349)
        ·
          refine ⟨1145503016184354001078753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6109349419649888005753349 1145503016184354001078753)
          ·
            refine ⟨859127262138265500809065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1145503016184354001078753 859127262138265500809065)
            ·
              refine ⟨644345446603699125606799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 859127262138265500809065 644345446603699125606799)
              ·
                refine ⟨966518169905548688410199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 644345446603699125606799 966518169905548688410199)
                ·
                  refine ⟨1449777254858323032615299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 966518169905548688410199 1449777254858323032615299)
                  ·
                    refine ⟨2174665882287484548922949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1449777254858323032615299 2174665882287484548922949)
                    ·
                      refine ⟨407749852928903352923053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2174665882287484548922949 407749852928903352923053)
                      ·
                        rfl

theorem cell23_794090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 2, 1, 1, 1, 4].length) (baseStart_794090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794090 prefixEnd_794090 := by exact prefixLift 794090
  have htrace : WordTrace (prefixWord ++ tailWord_794090) baseStart_794090 baseEnd_794090 := by
    simpa [prefixWord, tailWord_794090, baseEnd_794090] using wordTrace_append hprefix tailTrace_794090
  have hstable : (prefixWord ++ tailWord_794090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794090).length < 2 ^ (prefixWord ++ tailWord_794090).sum := by decide
  have hdescent : baseEnd_794090 < baseStart_794090 := by decide
  rcases family_descends (prefixWord ++ tailWord_794090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794092 : List Nat := [2, 2, 1, 1, 2, 1, 2, 2, 1, 9]
def baseStart_794092 : Nat := 118140960795 + 794092 * 2 ^ 59
def prefixEnd_794092 : Nat := 4983230072969 + 3 ^ 40 * 794092 * 2
def baseEnd_794092 : Nat := 135916959963404115032681

theorem tailTrace_794092 : CollatzResearch.WordTrace tailWord_794092 prefixEnd_794092 135916959963404115032681 := by
  unfold tailWord_794092
  simp only [CollatzResearch.WordTrace]
  refine ⟨14481457319573889480720265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19308609759431852640960353 14481457319573889480720265)
  ·
    refine ⟨10861092989680417110540199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14481457319573889480720265 10861092989680417110540199)
    ·
      refine ⟨16291639484520625665810299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10861092989680417110540199 16291639484520625665810299)
      ·
        refine ⟨24437459226780938498715449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16291639484520625665810299 24437459226780938498715449)
        ·
          refine ⟨18328094420085703874036587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24437459226780938498715449 18328094420085703874036587)
          ·
            refine ⟨27492141630128555811054881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18328094420085703874036587 27492141630128555811054881)
            ·
              refine ⟨20619106222596416858291161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27492141630128555811054881 20619106222596416858291161)
              ·
                refine ⟨15464329666947312643718371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20619106222596416858291161 15464329666947312643718371)
                ·
                  refine ⟨23196494500420968965577557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15464329666947312643718371 23196494500420968965577557)
                  ·
                    refine ⟨135916959963404115032681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 23196494500420968965577557 135916959963404115032681)
                    ·
                      rfl

theorem cell23_794092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 9].length) (baseStart_794092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794092 prefixEnd_794092 := by exact prefixLift 794092
  have htrace : WordTrace (prefixWord ++ tailWord_794092) baseStart_794092 baseEnd_794092 := by
    simpa [prefixWord, tailWord_794092, baseEnd_794092] using wordTrace_append hprefix tailTrace_794092
  have hstable : (prefixWord ++ tailWord_794092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794092).length < 2 ^ (prefixWord ++ tailWord_794092).sum := by decide
  have hdescent : baseEnd_794092 < baseStart_794092 := by decide
  rcases family_descends (prefixWord ++ tailWord_794092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794106 : List Nat := [3, 1, 1, 1, 1, 2, 5, 1, 4, 1, 3]
def baseStart_794106 : Nat := 118140960795 + 794106 * 2 ^ 59
def prefixEnd_794106 : Nat := 4983230072969 + 3 ^ 40 * 794106 * 2
def baseEnd_794106 : Nat := 407758068619375290322979

theorem tailTrace_794106 : CollatzResearch.WordTrace tailWord_794106 prefixEnd_794106 407758068619375290322979 := by
  unfold tailWord_794106
  simp only [CollatzResearch.WordTrace]
  refine ⟨7240856315274264838112543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19308950174064706234966781 7240856315274264838112543)
  ·
    refine ⟨10861284472911397257168815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7240856315274264838112543 10861284472911397257168815)
    ·
      refine ⟨16291926709367095885753223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10861284472911397257168815 16291926709367095885753223)
      ·
        refine ⟨24437890064050643828629835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16291926709367095885753223 24437890064050643828629835)
        ·
          refine ⟨36656835096075965742944753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24437890064050643828629835 36656835096075965742944753)
          ·
            refine ⟨27492626322056974307208565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36656835096075965742944753 27492626322056974307208565)
            ·
              refine ⟨2577433717692841341300803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27492626322056974307208565 2577433717692841341300803)
              ·
                refine ⟨3866150576539262011951205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2577433717692841341300803 3866150576539262011951205)
                ·
                  refine ⟨724903233101111627240851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3866150576539262011951205 724903233101111627240851)
                  ·
                    refine ⟨1087354849651667440861277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 724903233101111627240851 1087354849651667440861277)
                    ·
                      refine ⟨407758068619375290322979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1087354849651667440861277 407758068619375290322979)
                      ·
                        rfl

theorem cell23_794106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 4, 1, 3].length) (baseStart_794106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794106 prefixEnd_794106 := by exact prefixLift 794106
  have htrace : WordTrace (prefixWord ++ tailWord_794106) baseStart_794106 baseEnd_794106 := by
    simpa [prefixWord, tailWord_794106, baseEnd_794106] using wordTrace_append hprefix tailTrace_794106
  have hstable : (prefixWord ++ tailWord_794106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794106).length < 2 ^ (prefixWord ++ tailWord_794106).sum := by decide
  have hdescent : baseEnd_794106 < baseStart_794106 := by decide
  rcases family_descends (prefixWord ++ tailWord_794106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794123 : List Nat := [1, 1, 1, 1, 8, 2, 1, 1, 1, 3, 3]
def baseStart_794123 : Nat := 118140960795 + 794123 * 2 ^ 59
def prefixEnd_794123 : Nat := 4983230072969 + 3 ^ 40 * 794123 * 2
def baseEnd_794123 : Nat := 407766797790501723810401

theorem tailTrace_794123 : CollatzResearch.WordTrace tailWord_794123 prefixEnd_794123 407766797790501723810401 := by
  unfold tailWord_794123
  simp only [CollatzResearch.WordTrace]
  refine ⟨28964045302035471255819023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19309363534690314170546015 28964045302035471255819023)
  ·
    refine ⟨43446067953053206883728535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28964045302035471255819023 43446067953053206883728535)
    ·
      refine ⟨65169101929579810325592803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43446067953053206883728535 65169101929579810325592803)
      ·
        refine ⟨97753652894369715488389205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65169101929579810325592803 97753652894369715488389205)
        ·
          refine ⟨1145550619855895103379561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 97753652894369715488389205 1145550619855895103379561)
          ·
            refine ⟨859162964891921327534671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1145550619855895103379561 859162964891921327534671)
            ·
              refine ⟨1288744447337881991302007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 859162964891921327534671 1288744447337881991302007)
              ·
                refine ⟨1933116671006822986953011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1288744447337881991302007 1933116671006822986953011)
                ·
                  refine ⟨2899675006510234480429517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1933116671006822986953011 2899675006510234480429517)
                  ·
                    refine ⟨1087378127441337930161069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2899675006510234480429517 1087378127441337930161069)
                    ·
                      refine ⟨407766797790501723810401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1087378127441337930161069 407766797790501723810401)
                      ·
                        rfl

theorem cell23_794123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 1, 1, 3, 3].length) (baseStart_794123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794123 prefixEnd_794123 := by exact prefixLift 794123
  have htrace : WordTrace (prefixWord ++ tailWord_794123) baseStart_794123 baseEnd_794123 := by
    simpa [prefixWord, tailWord_794123, baseEnd_794123] using wordTrace_append hprefix tailTrace_794123
  have hstable : (prefixWord ++ tailWord_794123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794123).length < 2 ^ (prefixWord ++ tailWord_794123).sum := by decide
  have hdescent : baseEnd_794123 < baseStart_794123 := by decide
  rcases family_descends (prefixWord ++ tailWord_794123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794133 : List Nat := [1, 3, 2, 1, 3, 2, 1, 4, 1, 3, 2]
def baseStart_794133 : Nat := 118140960795 + 794133 * 2 ^ 59
def prefixEnd_794133 : Nat := 4983230072969 + 3 ^ 40 * 794133 * 2
def baseEnd_794133 : Nat := 407771932597046684685355

theorem tailTrace_794133 : CollatzResearch.WordTrace tailWord_794133 prefixEnd_794133 407771932597046684685355 := by
  unfold tailWord_794133
  simp only [CollatzResearch.WordTrace]
  refine ⟨28964410031999242963683053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19309606687999495309122035 28964410031999242963683053)
  ·
    refine ⟨10861653761999716111381145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28964410031999242963683053 10861653761999716111381145)
    ·
      refine ⟨8146240321499787083535859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10861653761999716111381145 8146240321499787083535859)
      ·
        refine ⟨12219360482249680625303789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8146240321499787083535859 12219360482249680625303789)
        ·
          refine ⟨4582260180843630234488921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12219360482249680625303789 4582260180843630234488921)
          ·
            refine ⟨3436695135632722675866691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4582260180843630234488921 3436695135632722675866691)
            ·
              refine ⟨5155042703449084013800037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3436695135632722675866691 5155042703449084013800037)
              ·
                refine ⟨966570506896703252587507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5155042703449084013800037 966570506896703252587507)
                ·
                  refine ⟨1449855760345054878881261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 966570506896703252587507 1449855760345054878881261)
                  ·
                    refine ⟨543695910129395579580473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1449855760345054878881261 543695910129395579580473)
                    ·
                      refine ⟨407771932597046684685355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 543695910129395579580473 407771932597046684685355)
                      ·
                        rfl

theorem cell23_794133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 4, 1, 3, 2].length) (baseStart_794133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794133 prefixEnd_794133 := by exact prefixLift 794133
  have htrace : WordTrace (prefixWord ++ tailWord_794133) baseStart_794133 baseEnd_794133 := by
    simpa [prefixWord, tailWord_794133, baseEnd_794133] using wordTrace_append hprefix tailTrace_794133
  have hstable : (prefixWord ++ tailWord_794133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794133).length < 2 ^ (prefixWord ++ tailWord_794133).sum := by decide
  have hdescent : baseEnd_794133 < baseStart_794133 := by decide
  rcases family_descends (prefixWord ++ tailWord_794133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794149 : List Nat := [1, 3, 1, 2, 2, 1, 1, 2, 1, 6, 3]
def baseStart_794149 : Nat := 118140960795 + 794149 * 2 ^ 59
def prefixEnd_794149 : Nat := 4983230072969 + 3 ^ 40 * 794149 * 2
def baseEnd_794149 : Nat := 407780148287518622085281

theorem tailTrace_794149 : CollatzResearch.WordTrace tailWord_794149 prefixEnd_794149 407780148287518622085281 := by
  unfold tailWord_794149
  simp only [CollatzResearch.WordTrace]
  refine ⟨28964993599941277696265501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19309995733294185130843667 28964993599941277696265501)
  ·
    refine ⟨10861872599977979136099563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28964993599941277696265501 10861872599977979136099563)
    ·
      refine ⟨16292808899966968704149345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10861872599977979136099563 16292808899966968704149345)
      ·
        refine ⟨12219606674975226528112009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16292808899966968704149345 12219606674975226528112009)
        ·
          refine ⟨9164705006231419896084007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12219606674975226528112009 9164705006231419896084007)
          ·
            refine ⟨13747057509347129844126011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9164705006231419896084007 13747057509347129844126011)
            ·
              refine ⟨20620586264020694766189017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13747057509347129844126011 20620586264020694766189017)
              ·
                refine ⟨15465439698015521074641763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20620586264020694766189017 15465439698015521074641763)
                ·
                  refine ⟨23198159547023281611962645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15465439698015521074641763 23198159547023281611962645)
                  ·
                    refine ⟨1087413728766716325560749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23198159547023281611962645 1087413728766716325560749)
                    ·
                      refine ⟨407780148287518622085281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1087413728766716325560749 407780148287518622085281)
                      ·
                        rfl

theorem cell23_794149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 6, 3].length) (baseStart_794149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794149 prefixEnd_794149 := by exact prefixLift 794149
  have htrace : WordTrace (prefixWord ++ tailWord_794149) baseStart_794149 baseEnd_794149 := by
    simpa [prefixWord, tailWord_794149, baseEnd_794149] using wordTrace_append hprefix tailTrace_794149
  have hstable : (prefixWord ++ tailWord_794149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794149).length < 2 ^ (prefixWord ++ tailWord_794149).sum := by decide
  have hdescent : baseEnd_794149 < baseStart_794149 := by decide
  rcases family_descends (prefixWord ++ tailWord_794149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794163 : List Nat := [1, 1, 1, 2, 4, 3, 2, 1, 4, 2, 2]
def baseStart_794163 : Nat := 118140960795 + 794163 * 2 ^ 59
def prefixEnd_794163 : Nat := 4983230072969 + 3 ^ 40 * 794163 * 2
def baseEnd_794163 : Nat := 407787337016681567310217

theorem tailTrace_794163 : CollatzResearch.WordTrace tailWord_794163 prefixEnd_794163 407787337016681567310217 := by
  unfold tailWord_794163
  simp only [CollatzResearch.WordTrace]
  refine ⟨28965504221890558087275143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19310336147927038724850095 28965504221890558087275143)
  ·
    refine ⟨43448256332835837130912715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28965504221890558087275143 43448256332835837130912715)
    ·
      refine ⟨65172384499253755696369073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43448256332835837130912715 65172384499253755696369073)
      ·
        refine ⟨48879288374440316772276805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65172384499253755696369073 48879288374440316772276805)
        ·
          refine ⟨9164866570207559394801901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48879288374440316772276805 9164866570207559394801901)
          ·
            refine ⟨3436824963827834773050713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9164866570207559394801901 3436824963827834773050713)
            ·
              refine ⟨2577618722870876079788035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3436824963827834773050713 2577618722870876079788035)
              ·
                refine ⟨3866428084306314119682053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2577618722870876079788035 3866428084306314119682053)
                ·
                  refine ⟨724955265807433897440385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3866428084306314119682053 724955265807433897440385)
                  ·
                    refine ⟨543716449355575423080289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 724955265807433897440385 543716449355575423080289)
                    ·
                      refine ⟨407787337016681567310217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 543716449355575423080289 407787337016681567310217)
                      ·
                        rfl

theorem cell23_794163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 4, 2, 2].length) (baseStart_794163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794163 prefixEnd_794163 := by exact prefixLift 794163
  have htrace : WordTrace (prefixWord ++ tailWord_794163) baseStart_794163 baseEnd_794163 := by
    simpa [prefixWord, tailWord_794163, baseEnd_794163] using wordTrace_append hprefix tailTrace_794163
  have hstable : (prefixWord ++ tailWord_794163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794163).length < 2 ^ (prefixWord ++ tailWord_794163).sum := by decide
  have hdescent : baseEnd_794163 < baseStart_794163 := by decide
  rcases family_descends (prefixWord ++ tailWord_794163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794209 : List Nat := [1, 2, 3, 1, 1, 3, 1, 1, 3, 2, 5]
def baseStart_794209 : Nat := 118140960795 + 794209 * 2 ^ 59
def prefixEnd_794209 : Nat := 4983230072969 + 3 ^ 40 * 794209 * 2
def baseEnd_794209 : Nat := 407810957126788387335005

theorem tailTrace_794209 : CollatzResearch.WordTrace tailWord_794209 prefixEnd_794209 407810957126788387335005 := by
  unfold tailWord_794209
  simp only [CollatzResearch.WordTrace]
  refine ⟨28967181979723907943449681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19311454653149271962299787 28967181979723907943449681)
  ·
    refine ⟨21725386484792930957587261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28967181979723907943449681 21725386484792930957587261)
    ·
      refine ⟨8147019931797349109095223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21725386484792930957587261 8147019931797349109095223)
      ·
        refine ⟨12220529897696023663642835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8147019931797349109095223 12220529897696023663642835)
        ·
          refine ⟨18330794846544035495464253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12220529897696023663642835 18330794846544035495464253)
          ·
            refine ⟨6874048067454013310799095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18330794846544035495464253 6874048067454013310799095)
            ·
              refine ⟨10311072101181019966198643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6874048067454013310799095 10311072101181019966198643)
              ·
                refine ⟨15466608151771529949297965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10311072101181019966198643 15466608151771529949297965)
                ·
                  refine ⟨5799978056914323730986737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15466608151771529949297965 5799978056914323730986737)
                  ·
                    refine ⟨4349983542685742798240053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5799978056914323730986737 4349983542685742798240053)
                    ·
                      refine ⟨407810957126788387335005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4349983542685742798240053 407810957126788387335005)
                      ·
                        rfl

theorem cell23_794209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_794209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794209 prefixEnd_794209 := by exact prefixLift 794209
  have htrace : WordTrace (prefixWord ++ tailWord_794209) baseStart_794209 baseEnd_794209 := by
    simpa [prefixWord, tailWord_794209, baseEnd_794209] using wordTrace_append hprefix tailTrace_794209
  have hstable : (prefixWord ++ tailWord_794209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794209).length < 2 ^ (prefixWord ++ tailWord_794209).sum := by decide
  have hdescent : baseEnd_794209 < baseStart_794209 := by decide
  rcases family_descends (prefixWord ++ tailWord_794209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794226 : List Nat := [3, 2, 1, 2, 3, 1, 2, 1, 1, 2, 5]
def baseStart_794226 : Nat := 118140960795 + 794226 * 2 ^ 59
def prefixEnd_794226 : Nat := 4983230072969 + 3 ^ 40 * 794226 * 2
def baseEnd_794226 : Nat := 407819686297914820822427

theorem tailTrace_794226 : CollatzResearch.WordTrace tailWord_794226 prefixEnd_794226 407819686297914820822427 := by
  unfold tailWord_794226
  simp only [CollatzResearch.WordTrace]
  refine ⟨7241950505165579961704633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19311868013774879897879021 7241950505165579961704633)
  ·
    refine ⟨5431462878874184971278475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7241950505165579961704633 5431462878874184971278475)
    ·
      refine ⟨8147194318311277456917713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5431462878874184971278475 8147194318311277456917713)
      ·
        refine ⟨6110395738733458092688285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8147194318311277456917713 6110395738733458092688285)
        ·
          refine ⟨2291398402025046784758107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6110395738733458092688285 2291398402025046784758107)
          ·
            refine ⟨3437097603037570177137161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2291398402025046784758107 3437097603037570177137161)
            ·
              refine ⟨2577823202278177632852871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3437097603037570177137161 2577823202278177632852871)
              ·
                refine ⟨3866734803417266449279307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2577823202278177632852871 3866734803417266449279307)
                ·
                  refine ⟨5800102205125899673918961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3866734803417266449279307 5800102205125899673918961)
                  ·
                    refine ⟨4350076653844424755439221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5800102205125899673918961 4350076653844424755439221)
                    ·
                      refine ⟨407819686297914820822427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4350076653844424755439221 407819686297914820822427)
                      ·
                        rfl

theorem cell23_794226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_794226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794226 prefixEnd_794226 := by exact prefixLift 794226
  have htrace : WordTrace (prefixWord ++ tailWord_794226) baseStart_794226 baseEnd_794226 := by
    simpa [prefixWord, tailWord_794226, baseEnd_794226] using wordTrace_append hprefix tailTrace_794226
  have hstable : (prefixWord ++ tailWord_794226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794226).length < 2 ^ (prefixWord ++ tailWord_794226).sum := by decide
  have hdescent : baseEnd_794226 < baseStart_794226 := by decide
  rcases family_descends (prefixWord ++ tailWord_794226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794270 : List Nat := [4, 3, 1, 1, 1, 2, 1, 2, 2, 4, 2]
def baseStart_794270 : Nat := 118140960795 + 794270 * 2 ^ 59
def prefixEnd_794270 : Nat := 4983230072969 + 3 ^ 40 * 794270 * 2
def baseEnd_794270 : Nat := 407842279446712648672225

theorem tailTrace_794270 : CollatzResearch.WordTrace tailWord_794270 prefixEnd_794270 407842279446712648672225 := by
  unfold tailWord_794270
  simp only [CollatzResearch.WordTrace]
  refine ⟨3621175854062864420177533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19312937888335276907613509 3621175854062864420177533)
  ·
    refine ⟨1357940945273574157566575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3621175854062864420177533 1357940945273574157566575)
    ·
      refine ⟨2036911417910361236349863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1357940945273574157566575 2036911417910361236349863)
      ·
        refine ⟨3055367126865541854524795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2036911417910361236349863 3055367126865541854524795)
        ·
          refine ⟨4583050690298312781787193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3055367126865541854524795 4583050690298312781787193)
          ·
            refine ⟨3437288017723734586340395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4583050690298312781787193 3437288017723734586340395)
            ·
              refine ⟨5155932026585601879510593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3437288017723734586340395 5155932026585601879510593)
              ·
                refine ⟨3866949019939201409632945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5155932026585601879510593 3866949019939201409632945)
                ·
                  refine ⟨2900211764954401057224709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3866949019939201409632945 2900211764954401057224709)
                  ·
                    refine ⟨543789705928950198229633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2900211764954401057224709 543789705928950198229633)
                    ·
                      refine ⟨407842279446712648672225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 543789705928950198229633 407842279446712648672225)
                      ·
                        rfl

theorem cell23_794270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_794270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794270 prefixEnd_794270 := by exact prefixLift 794270
  have htrace : WordTrace (prefixWord ++ tailWord_794270) baseStart_794270 baseEnd_794270 := by
    simpa [prefixWord, tailWord_794270, baseEnd_794270] using wordTrace_append hprefix tailTrace_794270
  have hstable : (prefixWord ++ tailWord_794270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794270).length < 2 ^ (prefixWord ++ tailWord_794270).sum := by decide
  have hdescent : baseEnd_794270 < baseStart_794270 := by decide
  rcases family_descends (prefixWord ++ tailWord_794270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794276 : List Nat := [2, 3, 1, 2, 2, 3, 1, 1, 8]
def baseStart_794276 : Nat := 118140960795 + 794276 * 2 ^ 59
def prefixEnd_794276 : Nat := 4983230072969 + 3 ^ 40 * 794276 * 2
def baseEnd_794276 : Nat := 45316151147848847244133

theorem tailTrace_794276 : CollatzResearch.WordTrace tailWord_794276 prefixEnd_794276 45316151147848847244133 := by
  unfold tailWord_794276
  simp only [CollatzResearch.WordTrace]
  refine ⟨14484812835240589193069341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19313083780320785590759121 14484812835240589193069341)
  ·
    refine ⟨5431804813215220947401003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14484812835240589193069341 5431804813215220947401003)
    ·
      refine ⟨8147707219822831421101505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5431804813215220947401003 8147707219822831421101505)
      ·
        refine ⟨6110780414867123565826129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8147707219822831421101505 6110780414867123565826129)
        ·
          refine ⟨4583085311150342674369597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6110780414867123565826129 4583085311150342674369597)
          ·
            refine ⟨1718656991681378502888599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4583085311150342674369597 1718656991681378502888599)
            ·
              refine ⟨2577985487522067754332899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1718656991681378502888599 2577985487522067754332899)
              ·
                refine ⟨3866978231283101631499349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2577985487522067754332899 3866978231283101631499349)
                ·
                  refine ⟨45316151147848847244133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3866978231283101631499349 45316151147848847244133)
                  ·
                    rfl

theorem cell23_794276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 8].length) (baseStart_794276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794276 prefixEnd_794276 := by exact prefixLift 794276
  have htrace : WordTrace (prefixWord ++ tailWord_794276) baseStart_794276 baseEnd_794276 := by
    simpa [prefixWord, tailWord_794276, baseEnd_794276] using wordTrace_append hprefix tailTrace_794276
  have hstable : (prefixWord ++ tailWord_794276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794276).length < 2 ^ (prefixWord ++ tailWord_794276).sum := by decide
  have hdescent : baseEnd_794276 < baseStart_794276 := by decide
  rcases family_descends (prefixWord ++ tailWord_794276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794299 : List Nat := [1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 7]
def baseStart_794299 : Nat := 118140960795 + 794299 * 2 ^ 59
def prefixEnd_794299 : Nat := 4983230072969 + 3 ^ 40 * 794299 * 2
def baseEnd_794299 : Nat := 407857170385693035209591

theorem tailTrace_794299 : CollatzResearch.WordTrace tailWord_794299 prefixEnd_794299 407857170385693035209591 := by
  unfold tailWord_794299
  simp only [CollatzResearch.WordTrace]
  refine ⟨28970464549397853314225951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19313643032931902209483967 28970464549397853314225951)
  ·
    refine ⟨43455696824096779971338927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28970464549397853314225951 43455696824096779971338927)
    ·
      refine ⟨65183545236145169957008391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43455696824096779971338927 65183545236145169957008391)
      ·
        refine ⟨97775317854217754935512587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65183545236145169957008391 97775317854217754935512587)
        ·
          refine ⟨146662976781326632403268881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97775317854217754935512587 146662976781326632403268881)
          ·
            refine ⟨109997232585994974302451661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146662976781326632403268881 109997232585994974302451661)
            ·
              refine ⟨41248962219748115363419373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109997232585994974302451661 41248962219748115363419373)
              ·
                refine ⟨15468360832405543261282265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41248962219748115363419373 15468360832405543261282265)
                ·
                  refine ⟨11601270624304157445961699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15468360832405543261282265 11601270624304157445961699)
                  ·
                    refine ⟨17401905936456236168942549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11601270624304157445961699 17401905936456236168942549)
                    ·
                      refine ⟨407857170385693035209591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 17401905936456236168942549 407857170385693035209591)
                      ·
                        rfl

theorem cell23_794299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 7].length) (baseStart_794299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794299 prefixEnd_794299 := by exact prefixLift 794299
  have htrace : WordTrace (prefixWord ++ tailWord_794299) baseStart_794299 baseEnd_794299 := by
    simpa [prefixWord, tailWord_794299, baseEnd_794299] using wordTrace_append hprefix tailTrace_794299
  have hstable : (prefixWord ++ tailWord_794299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794299).length < 2 ^ (prefixWord ++ tailWord_794299).sum := by decide
  have hdescent : baseEnd_794299 < baseStart_794299 := by decide
  rcases family_descends (prefixWord ++ tailWord_794299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794303 : List Nat := [1, 1, 2, 2, 2, 3, 1, 4, 3, 1, 3]
def baseStart_794303 : Nat := 118140960795 + 794303 * 2 ^ 59
def prefixEnd_794303 : Nat := 4983230072969 + 3 ^ 40 * 794303 * 2
def baseEnd_794303 : Nat := 407859224308311019559573

theorem tailTrace_794303 : CollatzResearch.WordTrace tailWord_794303 prefixEnd_794303 407859224308311019559573 := by
  unfold tailWord_794303
  simp only [CollatzResearch.WordTrace]
  refine ⟨28970610441383361997371563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19313740294255574664914375 28970610441383361997371563)
  ·
    refine ⟨43455915662075042996057345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28970610441383361997371563 43455915662075042996057345)
    ·
      refine ⟨32591936746556282247043009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43455915662075042996057345 32591936746556282247043009)
      ·
        refine ⟨24443952559917211685282257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32591936746556282247043009 24443952559917211685282257)
        ·
          refine ⟨18332964419937908763961693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24443952559917211685282257 18332964419937908763961693)
          ·
            refine ⟨6874861657476715786485635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18332964419937908763961693 6874861657476715786485635)
            ·
              refine ⟨10312292486215073679728453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6874861657476715786485635 10312292486215073679728453)
              ·
                refine ⟨1933554841165326314949085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10312292486215073679728453 1933554841165326314949085)
                ·
                  refine ⟨725083065436997368105907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1933554841165326314949085 725083065436997368105907)
                  ·
                    refine ⟨1087624598155496052158861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 725083065436997368105907 1087624598155496052158861)
                    ·
                      refine ⟨407859224308311019559573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1087624598155496052158861 407859224308311019559573)
                      ·
                        rfl

theorem cell23_794303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 4, 3, 1, 3].length) (baseStart_794303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794303 prefixEnd_794303 := by exact prefixLift 794303
  have htrace : WordTrace (prefixWord ++ tailWord_794303) baseStart_794303 baseEnd_794303 := by
    simpa [prefixWord, tailWord_794303, baseEnd_794303] using wordTrace_append hprefix tailTrace_794303
  have hstable : (prefixWord ++ tailWord_794303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794303).length < 2 ^ (prefixWord ++ tailWord_794303).sum := by decide
  have hdescent : baseEnd_794303 < baseStart_794303 := by decide
  rcases family_descends (prefixWord ++ tailWord_794303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794310 : List Nat := [6, 1, 2, 1, 1, 1, 1, 2, 8]
def baseStart_794310 : Nat := 118140960795 + 794310 * 2 ^ 59
def prefixEnd_794310 : Nat := 4983230072969 + 3 ^ 40 * 794310 * 2
def baseEnd_794310 : Nat := 45318090963654721352449

theorem tailTrace_794310 : CollatzResearch.WordTrace tailWord_794310 prefixEnd_794310 45318090963654721352449 := by
  unfold tailWord_794310
  simp only [CollatzResearch.WordTrace]
  refine ⟨905339554761187568527387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19313910501572001461917589 905339554761187568527387)
  ·
    refine ⟨1358009332141781352791081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 905339554761187568527387 1358009332141781352791081)
    ·
      refine ⟨1018506999106336014593311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1358009332141781352791081 1018506999106336014593311)
      ·
        refine ⟨1527760498659504021889967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1018506999106336014593311 1527760498659504021889967)
        ·
          refine ⟨2291640747989256032834951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1527760498659504021889967 2291640747989256032834951)
          ·
            refine ⟨3437461121983884049252427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2291640747989256032834951 3437461121983884049252427)
            ·
              refine ⟨5156191682975826073878641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3437461121983884049252427 5156191682975826073878641)
              ·
                refine ⟨3867143762231869555408981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5156191682975826073878641 3867143762231869555408981)
                ·
                  refine ⟨45318090963654721352449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3867143762231869555408981 45318090963654721352449)
                  ·
                    rfl

theorem cell23_794310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_794310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794310 prefixEnd_794310 := by exact prefixLift 794310
  have htrace : WordTrace (prefixWord ++ tailWord_794310) baseStart_794310 baseEnd_794310 := by
    simpa [prefixWord, tailWord_794310, baseEnd_794310] using wordTrace_append hprefix tailTrace_794310
  have hstable : (prefixWord ++ tailWord_794310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794310).length < 2 ^ (prefixWord ++ tailWord_794310).sum := by decide
  have hdescent : baseEnd_794310 < baseStart_794310 := by decide
  rcases family_descends (prefixWord ++ tailWord_794310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794314 : List Nat := [3, 1, 2, 1, 6, 1, 1, 3, 1, 4]
def baseStart_794314 : Nat := 118140960795 + 794314 * 2 ^ 59
def prefixEnd_794314 : Nat := 4983230072969 + 3 ^ 40 * 794314 * 2
def baseEnd_794314 : Nat := 135954957531836825507341

theorem tailTrace_794314 : CollatzResearch.WordTrace tailWord_794314 prefixEnd_794314 135954957531836825507341 := by
  unfold tailWord_794314
  simp only [CollatzResearch.WordTrace]
  refine ⟨7242752911085877719005499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19314007762895673917347997 7242752911085877719005499)
  ·
    refine ⟨10864129366628816578508249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7242752911085877719005499 10864129366628816578508249)
    ·
      refine ⟨8148097024971612433881187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10864129366628816578508249 8148097024971612433881187)
      ·
        refine ⟨12222145537457418650821781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8148097024971612433881187 12222145537457418650821781)
        ·
          refine ⟨572913072068316499257271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12222145537457418650821781 572913072068316499257271)
          ·
            refine ⟨859369608102474748885907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 572913072068316499257271 859369608102474748885907)
            ·
              refine ⟨1289054412153712123328861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 859369608102474748885907 1289054412153712123328861)
              ·
                refine ⟨483395404557642046248323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1289054412153712123328861 483395404557642046248323)
                ·
                  refine ⟨725093106836463069372485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 483395404557642046248323 725093106836463069372485)
                  ·
                    refine ⟨135954957531836825507341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 725093106836463069372485 135954957531836825507341)
                    ·
                      rfl

theorem cell23_794314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 3, 1, 4].length) (baseStart_794314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794314 prefixEnd_794314 := by exact prefixLift 794314
  have htrace : WordTrace (prefixWord ++ tailWord_794314) baseStart_794314 baseEnd_794314 := by
    simpa [prefixWord, tailWord_794314, baseEnd_794314] using wordTrace_append hprefix tailTrace_794314
  have hstable : (prefixWord ++ tailWord_794314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794314).length < 2 ^ (prefixWord ++ tailWord_794314).sum := by decide
  have hdescent : baseEnd_794314 < baseStart_794314 := by decide
  rcases family_descends (prefixWord ++ tailWord_794314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794320 : List Nat := [2, 1, 1, 1, 1, 2, 1, 9, 1, 1, 3]
def baseStart_794320 : Nat := 118140960795 + 794320 * 2 ^ 59
def prefixEnd_794320 : Nat := 4983230072969 + 3 ^ 40 * 794320 * 2
def baseEnd_794320 : Nat := 407867953479437453046995

theorem tailTrace_794320 : CollatzResearch.WordTrace tailWord_794320 prefixEnd_794320 407867953479437453046995 := by
  unfold tailWord_794320
  simp only [CollatzResearch.WordTrace]
  refine ⟨14485615241160886950370207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19314153654881182600493609 14485615241160886950370207)
  ·
    refine ⟨21728422861741330425555311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14485615241160886950370207 21728422861741330425555311)
    ·
      refine ⟨32592634292611995638332967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21728422861741330425555311 32592634292611995638332967)
      ·
        refine ⟨48888951438917993457499451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32592634292611995638332967 48888951438917993457499451)
        ·
          refine ⟨73333427158376990186249177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48888951438917993457499451 73333427158376990186249177)
          ·
            refine ⟨55000070368782742639686883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73333427158376990186249177 55000070368782742639686883)
            ·
              refine ⟨82500105553174113959530325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55000070368782742639686883 82500105553174113959530325)
              ·
                refine ⟨483399055975629573981623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 82500105553174113959530325 483399055975629573981623)
                ·
                  refine ⟨725098583963444360972435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 483399055975629573981623 725098583963444360972435)
                  ·
                    refine ⟨1087647875945166541458653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 725098583963444360972435 1087647875945166541458653)
                    ·
                      refine ⟨407867953479437453046995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1087647875945166541458653 407867953479437453046995)
                      ·
                        rfl

theorem cell23_794320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 9, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 9, 1, 1, 3].length) (baseStart_794320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794320 prefixEnd_794320 := by exact prefixLift 794320
  have htrace : WordTrace (prefixWord ++ tailWord_794320) baseStart_794320 baseEnd_794320 := by
    simpa [prefixWord, tailWord_794320, baseEnd_794320] using wordTrace_append hprefix tailTrace_794320
  have hstable : (prefixWord ++ tailWord_794320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794320).length < 2 ^ (prefixWord ++ tailWord_794320).sum := by decide
  have hdescent : baseEnd_794320 < baseStart_794320 := by decide
  rcases family_descends (prefixWord ++ tailWord_794320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794330 : List Nat := [3, 1, 1, 2, 2, 4, 1, 2, 2, 3, 2]
def baseStart_794330 : Nat := 118140960795 + 794330 * 2 ^ 59
def prefixEnd_794330 : Nat := 4983230072969 + 3 ^ 40 * 794330 * 2
def baseEnd_794330 : Nat := 407873088285982413921949

theorem tailTrace_794330 : CollatzResearch.WordTrace tailWord_794330 prefixEnd_794330 407873088285982413921949 := by
  unfold tailWord_794330
  simp only [CollatzResearch.WordTrace]
  refine ⟨7242898803071386402151111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19314396808190363739069629 7242898803071386402151111)
  ·
    refine ⟨10864348204607079603226667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7242898803071386402151111 10864348204607079603226667)
    ·
      refine ⟨16296522306910619404840001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10864348204607079603226667 16296522306910619404840001)
      ·
        refine ⟨12222391730182964553630001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16296522306910619404840001 12222391730182964553630001)
        ·
          refine ⟨9166793797637223415222501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12222391730182964553630001 9166793797637223415222501)
          ·
            refine ⟨1718773837056979390354219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9166793797637223415222501 1718773837056979390354219)
            ·
              refine ⟨2578160755585469085531329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1718773837056979390354219 2578160755585469085531329)
              ·
                refine ⟨1933620566689101814148497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2578160755585469085531329 1933620566689101814148497)
                ·
                  refine ⟨1450215425016826360611373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1933620566689101814148497 1450215425016826360611373)
                  ·
                    refine ⟨543830784381309885229265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1450215425016826360611373 543830784381309885229265)
                    ·
                      refine ⟨407873088285982413921949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 543830784381309885229265 407873088285982413921949)
                      ·
                        rfl

theorem cell23_794330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 2, 2, 3, 2].length) (baseStart_794330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794330 prefixEnd_794330 := by exact prefixLift 794330
  have htrace : WordTrace (prefixWord ++ tailWord_794330) baseStart_794330 baseEnd_794330 := by
    simpa [prefixWord, tailWord_794330, baseEnd_794330] using wordTrace_append hprefix tailTrace_794330
  have hstable : (prefixWord ++ tailWord_794330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794330).length < 2 ^ (prefixWord ++ tailWord_794330).sum := by decide
  have hdescent : baseEnd_794330 < baseStart_794330 := by decide
  rcases family_descends (prefixWord ++ tailWord_794330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794337 : List Nat := [1, 2, 3, 1, 5, 2, 1, 1, 3, 1, 3]
def baseStart_794337 : Nat := 118140960795 + 794337 * 2 ^ 59
def prefixEnd_794337 : Nat := 4983230072969 + 3 ^ 40 * 794337 * 2
def baseEnd_794337 : Nat := 407876682650563886534417

theorem tailTrace_794337 : CollatzResearch.WordTrace tailWord_794337 prefixEnd_794337 407876682650563886534417 := by
  unfold tailWord_794337
  simp only [CollatzResearch.WordTrace]
  refine ⟨28971850523260185804109265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19314567015506790536072843 28971850523260185804109265)
  ·
    refine ⟨21728887892445139353081949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28971850523260185804109265 21728887892445139353081949)
    ·
      refine ⟨8148332959666927257405731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21728887892445139353081949 8148332959666927257405731)
      ·
        refine ⟨12222499439500390886108597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8148332959666927257405731 12222499439500390886108597)
        ·
          refine ⟨1145859322453161645572681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12222499439500390886108597 1145859322453161645572681)
          ·
            refine ⟨859394491839871234179511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1145859322453161645572681 859394491839871234179511)
            ·
              refine ⟨1289091737759806851269267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 859394491839871234179511 1289091737759806851269267)
              ·
                refine ⟨1933637606639710276903901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1289091737759806851269267 1933637606639710276903901)
                ·
                  refine ⟨725114102489891353838963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1933637606639710276903901 725114102489891353838963)
                  ·
                    refine ⟨1087671153734837030758445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 725114102489891353838963 1087671153734837030758445)
                    ·
                      refine ⟨407876682650563886534417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1087671153734837030758445 407876682650563886534417)
                      ·
                        rfl

theorem cell23_794337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 1, 3, 1, 3].length) (baseStart_794337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794337 prefixEnd_794337 := by exact prefixLift 794337
  have htrace : WordTrace (prefixWord ++ tailWord_794337) baseStart_794337 baseEnd_794337 := by
    simpa [prefixWord, tailWord_794337, baseEnd_794337] using wordTrace_append hprefix tailTrace_794337
  have hstable : (prefixWord ++ tailWord_794337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794337).length < 2 ^ (prefixWord ++ tailWord_794337).sum := by decide
  have hdescent : baseEnd_794337 < baseStart_794337 := by decide
  rcases family_descends (prefixWord ++ tailWord_794337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794363 : List Nat := [1, 1, 1, 1, 1, 3, 1, 8, 1, 2, 3]
def baseStart_794363 : Nat := 118140960795 + 794363 * 2 ^ 59
def prefixEnd_794363 : Nat := 4983230072969 + 3 ^ 40 * 794363 * 2
def baseEnd_794363 : Nat := 407890033147580784809297

theorem tailTrace_794363 : CollatzResearch.WordTrace tailWord_794363 prefixEnd_794363 407890033147580784809297 := by
  unfold tailWord_794363
  simp only [CollatzResearch.WordTrace]
  refine ⟨28972798821165992244555743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19315199214110661496370495 28972798821165992244555743)
  ·
    refine ⟨43459198231748988366833615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28972798821165992244555743 43459198231748988366833615)
    ·
      refine ⟨65188797347623482550250423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43459198231748988366833615 65188797347623482550250423)
      ·
        refine ⟨97783196021435223825375635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65188797347623482550250423 97783196021435223825375635)
        ·
          refine ⟨146674794032152835738063453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97783196021435223825375635 146674794032152835738063453)
          ·
            refine ⟨55003047762057313401773795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146674794032152835738063453 55003047762057313401773795)
            ·
              refine ⟨82504571643085970102660693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55003047762057313401773795 82504571643085970102660693)
              ·
                refine ⟨966850448942413712140555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 82504571643085970102660693 966850448942413712140555)
                ·
                  refine ⟨1450275673413620568210833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 966850448942413712140555 1450275673413620568210833)
                  ·
                    refine ⟨1087706755060215426158125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1450275673413620568210833 1087706755060215426158125)
                    ·
                      refine ⟨407890033147580784809297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1087706755060215426158125 407890033147580784809297)
                      ·
                        rfl

theorem cell23_794363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 8, 1, 2, 3].length) (baseStart_794363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794363 prefixEnd_794363 := by exact prefixLift 794363
  have htrace : WordTrace (prefixWord ++ tailWord_794363) baseStart_794363 baseEnd_794363 := by
    simpa [prefixWord, tailWord_794363, baseEnd_794363] using wordTrace_append hprefix tailTrace_794363
  have hstable : (prefixWord ++ tailWord_794363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794363).length < 2 ^ (prefixWord ++ tailWord_794363).sum := by decide
  have hdescent : baseEnd_794363 < baseStart_794363 := by decide
  rcases family_descends (prefixWord ++ tailWord_794363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794377 : List Nat := [1, 2, 1, 1, 3, 2, 1, 7, 1, 2, 2]
def baseStart_794377 : Nat := 118140960795 + 794377 * 2 ^ 59
def prefixEnd_794377 : Nat := 4983230072969 + 3 ^ 40 * 794377 * 2
def baseEnd_794377 : Nat := 407897221876743730034233

theorem tailTrace_794377 : CollatzResearch.WordTrace tailWord_794377 prefixEnd_794377 407897221876743730034233 := by
  unfold tailWord_794377
  simp only [CollatzResearch.WordTrace]
  refine ⟨28973309443115272635565385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19315539628743515090376923 28973309443115272635565385)
  ·
    refine ⟨21729982082336454476674039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28973309443115272635565385 21729982082336454476674039)
    ·
      refine ⟨32594973123504681715011059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21729982082336454476674039 32594973123504681715011059)
      ·
        refine ⟨48892459685257022572516589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32594973123504681715011059 48892459685257022572516589)
        ·
          refine ⟨18334672381971383464693721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48892459685257022572516589 18334672381971383464693721)
          ·
            refine ⟨13751004286478537598520291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18334672381971383464693721 13751004286478537598520291)
            ·
              refine ⟨20626506429717806397780437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13751004286478537598520291 20626506429717806397780437)
              ·
                refine ⟨483433744446511087447979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 20626506429717806397780437 483433744446511087447979)
                ·
                  refine ⟨725150616669766631171969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 483433744446511087447979 725150616669766631171969)
                  ·
                    refine ⟨543862962502324973378977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 725150616669766631171969 543862962502324973378977)
                    ·
                      refine ⟨407897221876743730034233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 543862962502324973378977 407897221876743730034233)
                      ·
                        rfl

theorem cell23_794377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 7, 1, 2, 2].length) (baseStart_794377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794377 prefixEnd_794377 := by exact prefixLift 794377
  have htrace : WordTrace (prefixWord ++ tailWord_794377) baseStart_794377 baseEnd_794377 := by
    simpa [prefixWord, tailWord_794377, baseEnd_794377] using wordTrace_append hprefix tailTrace_794377
  have hstable : (prefixWord ++ tailWord_794377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794377).length < 2 ^ (prefixWord ++ tailWord_794377).sum := by decide
  have hdescent : baseEnd_794377 < baseStart_794377 := by decide
  rcases family_descends (prefixWord ++ tailWord_794377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794388 : List Nat := [2, 4, 4, 1, 1, 1, 1, 4, 1, 1, 3]
def baseStart_794388 : Nat := 118140960795 + 794388 * 2 ^ 59
def prefixEnd_794388 : Nat := 4983230072969 + 3 ^ 40 * 794388 * 2
def baseEnd_794388 : Nat := 407902870163943186996683

theorem tailTrace_794388 : CollatzResearch.WordTrace tailWord_794388 prefixEnd_794388 407902870163943186996683 := by
  unfold tailWord_794388
  simp only [CollatzResearch.WordTrace]
  refine ⟨14486855323037710757107909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19315807097383614342810545 14486855323037710757107909)
  ·
    refine ⟨2716285373069570766957733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14486855323037710757107909 2716285373069570766957733)
    ·
      refine ⟨509303507450544518804575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2716285373069570766957733 509303507450544518804575)
      ·
        refine ⟨763955261175816778206863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 509303507450544518804575 763955261175816778206863)
        ·
          refine ⟨1145932891763725167310295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 763955261175816778206863 1145932891763725167310295)
          ·
            refine ⟨1718899337645587750965443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1145932891763725167310295 1718899337645587750965443)
            ·
              refine ⟨2578349006468381626448165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1718899337645587750965443 2578349006468381626448165)
              ·
                refine ⟨483440438712821554959031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2578349006468381626448165 483440438712821554959031)
                ·
                  refine ⟨725160658069232332438547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 483440438712821554959031 725160658069232332438547)
                  ·
                    refine ⟨1087740987103848498657821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 725160658069232332438547 1087740987103848498657821)
                    ·
                      refine ⟨407902870163943186996683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1087740987103848498657821 407902870163943186996683)
                      ·
                        rfl

theorem cell23_794388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_794388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794388 prefixEnd_794388 := by exact prefixLift 794388
  have htrace : WordTrace (prefixWord ++ tailWord_794388) baseStart_794388 baseEnd_794388 := by
    simpa [prefixWord, tailWord_794388, baseEnd_794388] using wordTrace_append hprefix tailTrace_794388
  have hstable : (prefixWord ++ tailWord_794388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794388).length < 2 ^ (prefixWord ++ tailWord_794388).sum := by decide
  have hdescent : baseEnd_794388 < baseStart_794388 := by decide
  rcases family_descends (prefixWord ++ tailWord_794388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794393 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 8, 1, 3]
def baseStart_794393 : Nat := 118140960795 + 794393 * 2 ^ 59
def prefixEnd_794393 : Nat := 4983230072969 + 3 ^ 40 * 794393 * 2
def baseEnd_794393 : Nat := 407905437567215667434159

theorem tailTrace_794393 : CollatzResearch.WordTrace tailWord_794393 prefixEnd_794393 407905437567215667434159 := by
  unfold tailWord_794393
  simp only [CollatzResearch.WordTrace]
  refine ⟨28973893011057307368147833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19315928674038204912098555 28973893011057307368147833)
  ·
    refine ⟨21730419758292980526110875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28973893011057307368147833 21730419758292980526110875)
    ·
      refine ⟨32595629637439470789166313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21730419758292980526110875 32595629637439470789166313)
      ·
        refine ⟨24446722228079603091874735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32595629637439470789166313 24446722228079603091874735)
        ·
          refine ⟨36670083342119404637812103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24446722228079603091874735 36670083342119404637812103)
          ·
            refine ⟨55005125013179106956718155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36670083342119404637812103 55005125013179106956718155)
            ·
              refine ⟨82507687519768660435077233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55005125013179106956718155 82507687519768660435077233)
              ·
                refine ⟨61880765639826495326307925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82507687519768660435077233 61880765639826495326307925)
                ·
                  refine ⟨725165222341716742105171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 61880765639826495326307925 725165222341716742105171)
                  ·
                    refine ⟨1087747833512575113157757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 725165222341716742105171 1087747833512575113157757)
                    ·
                      refine ⟨407905437567215667434159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1087747833512575113157757 407905437567215667434159)
                      ·
                        rfl

theorem cell23_794393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 8, 1, 3].length) (baseStart_794393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794393 prefixEnd_794393 := by exact prefixLift 794393
  have htrace : WordTrace (prefixWord ++ tailWord_794393) baseStart_794393 baseEnd_794393 := by
    simpa [prefixWord, tailWord_794393, baseEnd_794393] using wordTrace_append hprefix tailTrace_794393
  have hstable : (prefixWord ++ tailWord_794393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794393).length < 2 ^ (prefixWord ++ tailWord_794393).sum := by decide
  have hdescent : baseEnd_794393 < baseStart_794393 := by decide
  rcases family_descends (prefixWord ++ tailWord_794393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794394 : List Nat := [3, 1, 1, 3, 2, 3, 1, 4, 1, 2, 2]
def baseStart_794394 : Nat := 118140960795 + 794394 * 2 ^ 59
def prefixEnd_794394 : Nat := 4983230072969 + 3 ^ 40 * 794394 * 2
def baseEnd_794394 : Nat := 407905951047870163521655

theorem tailTrace_794394 : CollatzResearch.WordTrace tailWord_794394 prefixEnd_794394 407905951047870163521655 := by
  unfold tailWord_794394
  simp only [CollatzResearch.WordTrace]
  refine ⟨7243482371013421134733559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19315952989369123025956157 7243482371013421134733559)
  ·
    refine ⟨10865223556520131702100339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7243482371013421134733559 10865223556520131702100339)
    ·
      refine ⟨16297835334780197553150509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10865223556520131702100339 16297835334780197553150509)
      ·
        refine ⟨6111688250542574082431441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16297835334780197553150509 6111688250542574082431441)
        ·
          refine ⟨4583766187906930561823581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6111688250542574082431441 4583766187906930561823581)
          ·
            refine ⟨1718912320465098960683843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4583766187906930561823581 1718912320465098960683843)
            ·
              refine ⟨2578368480697648441025765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1718912320465098960683843 2578368480697648441025765)
              ·
                refine ⟨483444090130809082692331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2578368480697648441025765 483444090130809082692331)
                ·
                  refine ⟨725166135196213624038497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 483444090130809082692331 725166135196213624038497)
                  ·
                    refine ⟨543874601397160218028873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 725166135196213624038497 543874601397160218028873)
                    ·
                      refine ⟨407905951047870163521655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 543874601397160218028873 407905951047870163521655)
                      ·
                        rfl

theorem cell23_794394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 4, 1, 2, 2].length) (baseStart_794394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794394 prefixEnd_794394 := by exact prefixLift 794394
  have htrace : WordTrace (prefixWord ++ tailWord_794394) baseStart_794394 baseEnd_794394 := by
    simpa [prefixWord, tailWord_794394, baseEnd_794394] using wordTrace_append hprefix tailTrace_794394
  have hstable : (prefixWord ++ tailWord_794394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794394).length < 2 ^ (prefixWord ++ tailWord_794394).sum := by decide
  have hdescent : baseEnd_794394 < baseStart_794394 := by decide
  rcases family_descends (prefixWord ++ tailWord_794394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794396 : List Nat := [2, 2, 3, 1, 1, 2, 1, 1, 1, 9]
def baseStart_794396 : Nat := 118140960795 + 794396 * 2 ^ 59
def prefixEnd_794396 : Nat := 4983230072969 + 3 ^ 40 * 794396 * 2
def baseEnd_794396 : Nat := 135968992669726385232215

theorem tailTrace_794396 : CollatzResearch.WordTrace tailWord_794396 prefixEnd_794396 135968992669726385232215 := by
  unfold tailWord_794396
  simp only [CollatzResearch.WordTrace]
  refine ⟨14487001215023219440253521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19316001620030959253671361 14487001215023219440253521)
  ·
    refine ⟨10865250911267414580190141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14487001215023219440253521 10865250911267414580190141)
    ·
      refine ⟨4074469091725280467571303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10865250911267414580190141 4074469091725280467571303)
      ·
        refine ⟨6111703637587920701356955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4074469091725280467571303 6111703637587920701356955)
        ·
          refine ⟨9167555456381881052035433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6111703637587920701356955 9167555456381881052035433)
          ·
            refine ⟨6875666592286410789026575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9167555456381881052035433 6875666592286410789026575)
            ·
              refine ⟨10313499888429616183539863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6875666592286410789026575 10313499888429616183539863)
              ·
                refine ⟨15470249832644424275309795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10313499888429616183539863 15470249832644424275309795)
                ·
                  refine ⟨23205374748966636412964693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15470249832644424275309795 23205374748966636412964693)
                  ·
                    refine ⟨135968992669726385232215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 23205374748966636412964693 135968992669726385232215)
                    ·
                      rfl

theorem cell23_794396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_794396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794396 prefixEnd_794396 := by exact prefixLift 794396
  have htrace : WordTrace (prefixWord ++ tailWord_794396) baseStart_794396 baseEnd_794396 := by
    simpa [prefixWord, tailWord_794396, baseEnd_794396] using wordTrace_append hprefix tailTrace_794396
  have hstable : (prefixWord ++ tailWord_794396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794396).length < 2 ^ (prefixWord ++ tailWord_794396).sum := by decide
  have hdescent : baseEnd_794396 < baseStart_794396 := by decide
  rcases family_descends (prefixWord ++ tailWord_794396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794444 : List Nat := [2, 2, 1, 3, 4, 2, 1, 2, 2, 1, 3]
def baseStart_794444 : Nat := 118140960795 + 794444 * 2 ^ 59
def prefixEnd_794444 : Nat := 4983230072969 + 3 ^ 40 * 794444 * 2
def baseEnd_794444 : Nat := 407931625080594967896425

theorem tailTrace_794444 : CollatzResearch.WordTrace tailWord_794444 prefixEnd_794444 407931625080594967896425 := by
  unfold tailWord_794444
  simp only [CollatzResearch.WordTrace]
  refine ⟨14487876566936271539127193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19317168755915028718836257 14487876566936271539127193)
  ·
    refine ⟨10865907425202203654345395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14487876566936271539127193 10865907425202203654345395)
    ·
      refine ⟨16298861137803305481518093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10865907425202203654345395 16298861137803305481518093)
      ·
        refine ⟨6112072926676239555569285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16298861137803305481518093 6112072926676239555569285)
        ·
          refine ⟨1146013673751794916669241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6112072926676239555569285 1146013673751794916669241)
          ·
            refine ⟨859510255313846187501931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1146013673751794916669241 859510255313846187501931)
            ·
              refine ⟨1289265382970769281252897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 859510255313846187501931 1289265382970769281252897)
              ·
                refine ⟨966949037228076960939673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1289265382970769281252897 966949037228076960939673)
                ·
                  refine ⟨725211777921057720704755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 966949037228076960939673 725211777921057720704755)
                  ·
                    refine ⟨1087817666881586581057133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 725211777921057720704755 1087817666881586581057133)
                    ·
                      refine ⟨407931625080594967896425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1087817666881586581057133 407931625080594967896425)
                      ·
                        rfl

theorem cell23_794444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 2, 2, 1, 3].length) (baseStart_794444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794444 prefixEnd_794444 := by exact prefixLift 794444
  have htrace : WordTrace (prefixWord ++ tailWord_794444) baseStart_794444 baseEnd_794444 := by
    simpa [prefixWord, tailWord_794444, baseEnd_794444] using wordTrace_append hprefix tailTrace_794444
  have hstable : (prefixWord ++ tailWord_794444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794444).length < 2 ^ (prefixWord ++ tailWord_794444).sum := by decide
  have hdescent : baseEnd_794444 < baseStart_794444 := by decide
  rcases family_descends (prefixWord ++ tailWord_794444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794463 : List Nat := [1, 1, 2, 3, 1, 4, 2, 1, 2, 2, 4]
def baseStart_794463 : Nat := 118140960795 + 794463 * 2 ^ 59
def prefixEnd_794463 : Nat := 4983230072969 + 3 ^ 40 * 794463 * 2
def baseEnd_794463 : Nat := 407941381213030393558837

theorem tailTrace_794463 : CollatzResearch.WordTrace tailWord_794463 prefixEnd_794463 407941381213030393558837 := by
  unfold tailWord_794463
  simp only [CollatzResearch.WordTrace]
  refine ⟨28976446120803709323196043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19317630747202472882130695 28976446120803709323196043)
  ·
    refine ⟨43464669181205563984794065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28976446120803709323196043 43464669181205563984794065)
    ·
      refine ⟨32598501885904172988595549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43464669181205563984794065 32598501885904172988595549)
      ·
        refine ⟨12224438207214064870723331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32598501885904172988595549 12224438207214064870723331)
        ·
          refine ⟨18336657310821097306084997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12224438207214064870723331 18336657310821097306084997)
          ·
            refine ⟨3438123245778955744890937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18336657310821097306084997 3438123245778955744890937)
            ·
              refine ⟨2578592434334216808668203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3438123245778955744890937 2578592434334216808668203)
              ·
                refine ⟨3867888651501325213002305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2578592434334216808668203 3867888651501325213002305)
                ·
                  refine ⟨2900916488625993909751729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3867888651501325213002305 2900916488625993909751729)
                  ·
                    refine ⟨2175687366469495432313797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2900916488625993909751729 2175687366469495432313797)
                    ·
                      refine ⟨407941381213030393558837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2175687366469495432313797 407941381213030393558837)
                      ·
                        rfl

theorem cell23_794463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_794463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794463 prefixEnd_794463 := by exact prefixLift 794463
  have htrace : WordTrace (prefixWord ++ tailWord_794463) baseStart_794463 baseEnd_794463 := by
    simpa [prefixWord, tailWord_794463, baseEnd_794463] using wordTrace_append hprefix tailTrace_794463
  have hstable : (prefixWord ++ tailWord_794463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794463).length < 2 ^ (prefixWord ++ tailWord_794463).sum := by decide
  have hdescent : baseEnd_794463 < baseStart_794463 := by decide
  rcases family_descends (prefixWord ++ tailWord_794463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794490 : List Nat := [3, 1, 1, 1, 1, 1, 7, 3, 5]
def baseStart_794490 : Nat := 118140960795 + 794490 * 2 ^ 59
def prefixEnd_794490 : Nat := 4983230072969 + 3 ^ 40 * 794490 * 2
def baseEnd_794490 : Nat := 45328360576744643102357

theorem tailTrace_794490 : CollatzResearch.WordTrace tailWord_794490 prefixEnd_794490 45328360576744643102357 := by
  unfold tailWord_794490
  simp only [CollatzResearch.WordTrace]
  refine ⟨7244357722926473233607231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19318287261137261956285949 7244357722926473233607231)
  ·
    refine ⟨10866536584389709850410847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7244357722926473233607231 10866536584389709850410847)
    ·
      refine ⟨16299804876584564775616271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10866536584389709850410847 16299804876584564775616271)
      ·
        refine ⟨24449707314876847163424407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16299804876584564775616271 24449707314876847163424407)
        ·
          refine ⟨36674560972315270745136611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24449707314876847163424407 36674560972315270745136611)
          ·
            refine ⟨55011841458472906117704917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36674560972315270745136611 55011841458472906117704917)
            ·
              refine ⟨1289340034182958737133709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 55011841458472906117704917 1289340034182958737133709)
              ·
                refine ⟨483502512818609526425141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1289340034182958737133709 483502512818609526425141)
                ·
                  refine ⟨45328360576744643102357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 483502512818609526425141 45328360576744643102357)
                  ·
                    rfl

theorem cell23_794490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 3, 5].length) (baseStart_794490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794490 prefixEnd_794490 := by exact prefixLift 794490
  have htrace : WordTrace (prefixWord ++ tailWord_794490) baseStart_794490 baseEnd_794490 := by
    simpa [prefixWord, tailWord_794490, baseEnd_794490] using wordTrace_append hprefix tailTrace_794490
  have hstable : (prefixWord ++ tailWord_794490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794490).length < 2 ^ (prefixWord ++ tailWord_794490).sum := by decide
  have hdescent : baseEnd_794490 < baseStart_794490 := by decide
  rcases family_descends (prefixWord ++ tailWord_794490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794553 : List Nat := [1, 2, 1, 4, 2, 1, 2, 1, 2, 1, 6]
def baseStart_794553 : Nat := 118140960795 + 794553 * 2 ^ 59
def prefixEnd_794553 : Nat := 4983230072969 + 3 ^ 40 * 794553 * 2
def baseEnd_794553 : Nat := 407987594471935041433423

theorem tailTrace_794553 : CollatzResearch.WordTrace tailWord_794553 prefixEnd_794553 407987594471935041433423 := by
  unfold tailWord_794553
  simp only [CollatzResearch.WordTrace]
  refine ⟨28979728690477654693972313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19319819126985103129314875 28979728690477654693972313)
  ·
    refine ⟨21734796517858241020479235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28979728690477654693972313 21734796517858241020479235)
    ·
      refine ⟨32602194776787361530718853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21734796517858241020479235 32602194776787361530718853)
      ·
        refine ⟨6112911520647630287009785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32602194776787361530718853 6112911520647630287009785)
        ·
          refine ⟨4584683640485722715257339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6112911520647630287009785 4584683640485722715257339)
          ·
            refine ⟨6877025460728584072886009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4584683640485722715257339 6877025460728584072886009)
            ·
              refine ⟨5157769095546438054664507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6877025460728584072886009 5157769095546438054664507)
              ·
                refine ⟨7736653643319657081996761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5157769095546438054664507 7736653643319657081996761)
                ·
                  refine ⟨5802490232489742811497571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7736653643319657081996761 5802490232489742811497571)
                  ·
                    refine ⟨8703735348734614217246357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5802490232489742811497571 8703735348734614217246357)
                    ·
                      refine ⟨407987594471935041433423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8703735348734614217246357 407987594471935041433423)
                      ·
                        rfl

theorem cell23_794553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_794553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794553 prefixEnd_794553 := by exact prefixLift 794553
  have htrace : WordTrace (prefixWord ++ tailWord_794553) baseStart_794553 baseEnd_794553 := by
    simpa [prefixWord, tailWord_794553, baseEnd_794553] using wordTrace_append hprefix tailTrace_794553
  have hstable : (prefixWord ++ tailWord_794553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794553).length < 2 ^ (prefixWord ++ tailWord_794553).sum := by decide
  have hdescent : baseEnd_794553 < baseStart_794553 := by decide
  rcases family_descends (prefixWord ++ tailWord_794553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794560 : List Nat := [2, 1, 1, 2, 3, 2, 1, 4, 2, 2, 3]
def baseStart_794560 : Nat := 118140960795 + 794560 * 2 ^ 59
def prefixEnd_794560 : Nat := 4983230072969 + 3 ^ 40 * 794560 * 2
def baseEnd_794560 : Nat := 407991188836516514045891

theorem tailTrace_794560 : CollatzResearch.WordTrace tailWord_794560 prefixEnd_794560 407991188836516514045891 := by
  unfold tailWord_794560
  simp only [CollatzResearch.WordTrace]
  refine ⟨14489992000726147444738567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19319989334301529926318089 14489992000726147444738567)
  ·
    refine ⟨21734988001089221167107851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14489992000726147444738567 21734988001089221167107851)
    ·
      refine ⟨32602482001633831750661777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21734988001089221167107851 32602482001633831750661777)
      ·
        refine ⟨24451861501225373812996333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32602482001633831750661777 24451861501225373812996333)
        ·
          refine ⟨9169448062959515179873625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24451861501225373812996333 9169448062959515179873625)
          ·
            refine ⟨6877086047219636384905219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9169448062959515179873625 6877086047219636384905219)
            ·
              refine ⟨10315629070829454577357829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6877086047219636384905219 10315629070829454577357829)
              ·
                refine ⟨1934180450780522733254593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10315629070829454577357829 1934180450780522733254593)
                ·
                  refine ⟨1450635338085392049940945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1934180450780522733254593 1450635338085392049940945)
                  ·
                    refine ⟨1087976503564044037455709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1450635338085392049940945 1087976503564044037455709)
                    ·
                      refine ⟨407991188836516514045891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1087976503564044037455709 407991188836516514045891)
                      ·
                        rfl

theorem cell23_794560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 4, 2, 2, 3].length) (baseStart_794560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794560 prefixEnd_794560 := by exact prefixLift 794560
  have htrace : WordTrace (prefixWord ++ tailWord_794560) baseStart_794560 baseEnd_794560 := by
    simpa [prefixWord, tailWord_794560, baseEnd_794560] using wordTrace_append hprefix tailTrace_794560
  have hstable : (prefixWord ++ tailWord_794560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794560).length < 2 ^ (prefixWord ++ tailWord_794560).sum := by decide
  have hdescent : baseEnd_794560 < baseStart_794560 := by decide
  rcases family_descends (prefixWord ++ tailWord_794560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794580 : List Nat := [2, 4, 1, 2, 1, 1, 1, 5, 6]
def baseStart_794580 : Nat := 118140960795 + 794580 * 2 ^ 59
def prefixEnd_794580 : Nat := 4983230072969 + 3 ^ 40 * 794580 * 2
def baseEnd_794580 : Nat := 45333495383289603977311

theorem tailTrace_794580 : CollatzResearch.WordTrace tailWord_794580 prefixEnd_794580 45333495383289603977311 := by
  unfold tailWord_794580
  simp only [CollatzResearch.WordTrace]
  refine ⟨14490356730689919152602597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19320475640919892203470129 14490356730689919152602597)
  ·
    refine ⟨2716941887004359841112987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14490356730689919152602597 2716941887004359841112987)
    ·
      refine ⟨4075412830506539761669481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2716941887004359841112987 4075412830506539761669481)
      ·
        refine ⟨3056559622879904821252111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4075412830506539761669481 3056559622879904821252111)
        ·
          refine ⟨4584839434319857231878167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3056559622879904821252111 4584839434319857231878167)
          ·
            refine ⟨6877259151479785847817251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4584839434319857231878167 6877259151479785847817251)
            ·
              refine ⟨10315888727219678771725877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6877259151479785847817251 10315888727219678771725877)
              ·
                refine ⟨967114568176844884849301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10315888727219678771725877 967114568176844884849301)
                ·
                  refine ⟨45333495383289603977311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 967114568176844884849301 45333495383289603977311)
                  ·
                    rfl

theorem cell23_794580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 5, 6].length) (baseStart_794580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794580 prefixEnd_794580 := by exact prefixLift 794580
  have htrace : WordTrace (prefixWord ++ tailWord_794580) baseStart_794580 baseEnd_794580 := by
    simpa [prefixWord, tailWord_794580, baseEnd_794580] using wordTrace_append hprefix tailTrace_794580
  have hstable : (prefixWord ++ tailWord_794580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794580).length < 2 ^ (prefixWord ++ tailWord_794580).sum := by decide
  have hdescent : baseEnd_794580 < baseStart_794580 := by decide
  rcases family_descends (prefixWord ++ tailWord_794580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794588 : List Nat := [2, 2, 6, 1, 2, 1, 1, 1, 2, 5]
def baseStart_794588 : Nat := 118140960795 + 794588 * 2 ^ 59
def prefixEnd_794588 : Nat := 4983230072969 + 3 ^ 40 * 794588 * 2
def baseEnd_794588 : Nat := 136001855431614134831921

theorem tailTrace_794588 : CollatzResearch.WordTrace tailWord_794588 prefixEnd_794588 136001855431614134831921 := by
  unfold tailWord_794588
  simp only [CollatzResearch.WordTrace]
  refine ⟨14490502622675427835748209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19320670163567237114330945 14490502622675427835748209)
  ·
    refine ⟨10867876967006570876811157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14490502622675427835748209 10867876967006570876811157)
    ·
      refine ⟨509431732828433009850523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10867876967006570876811157 509431732828433009850523)
      ·
        refine ⟨764147599242649514775785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 509431732828433009850523 764147599242649514775785)
        ·
          refine ⟨573110699431987136081839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 764147599242649514775785 573110699431987136081839)
          ·
            refine ⟨859666049147980704122759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 573110699431987136081839 859666049147980704122759)
            ·
              refine ⟨1289499073721971056184139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 859666049147980704122759 1289499073721971056184139)
              ·
                refine ⟨1934248610582956584276209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1289499073721971056184139 1934248610582956584276209)
                ·
                  refine ⟨1450686457937217438207157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1934248610582956584276209 1450686457937217438207157)
                  ·
                    refine ⟨136001855431614134831921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1450686457937217438207157 136001855431614134831921)
                    ·
                      rfl

theorem cell23_794588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_794588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794588 prefixEnd_794588 := by exact prefixLift 794588
  have htrace : WordTrace (prefixWord ++ tailWord_794588) baseStart_794588 baseEnd_794588 := by
    simpa [prefixWord, tailWord_794588, baseEnd_794588] using wordTrace_append hprefix tailTrace_794588
  have hstable : (prefixWord ++ tailWord_794588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794588).length < 2 ^ (prefixWord ++ tailWord_794588).sum := by decide
  have hdescent : baseEnd_794588 < baseStart_794588 := by decide
  rcases family_descends (prefixWord ++ tailWord_794588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794594 : List Nat := [3, 3, 3, 1, 2, 1, 1, 1, 1, 4, 3]
def baseStart_794594 : Nat := 118140960795 + 794594 * 2 ^ 59
def prefixEnd_794594 : Nat := 4983230072969 + 3 ^ 40 * 794594 * 2
def baseEnd_794594 : Nat := 408008647178769381020735

theorem tailTrace_794594 : CollatzResearch.WordTrace tailWord_794594 prefixEnd_794594 408008647178769381020735 := by
  unfold tailWord_794594
  simp only [CollatzResearch.WordTrace]
  refine ⟨7245306020832279674053709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19320816055552745797476557 7245306020832279674053709)
  ·
    refine ⟨2716989757812104877770141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7245306020832279674053709 2716989757812104877770141)
    ·
      refine ⟨1018871159179539329163803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2716989757812104877770141 1018871159179539329163803)
      ·
        refine ⟨1528306738769308993745705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1018871159179539329163803 1528306738769308993745705)
        ·
          refine ⟨1146230054076981745309279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1528306738769308993745705 1146230054076981745309279)
          ·
            refine ⟨1719345081115472617963919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1146230054076981745309279 1719345081115472617963919)
            ·
              refine ⟨2579017621673208926945879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1719345081115472617963919 2579017621673208926945879)
              ·
                refine ⟨3868526432509813390418819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2579017621673208926945879 3868526432509813390418819)
                ·
                  refine ⟨5802789648764720085628229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3868526432509813390418819 5802789648764720085628229)
                  ·
                    refine ⟨1088023059143385016055293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5802789648764720085628229 1088023059143385016055293)
                    ·
                      refine ⟨408008647178769381020735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1088023059143385016055293 408008647178769381020735)
                      ·
                        rfl

theorem cell23_794594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_794594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794594 prefixEnd_794594 := by exact prefixLift 794594
  have htrace : WordTrace (prefixWord ++ tailWord_794594) baseStart_794594 baseEnd_794594 := by
    simpa [prefixWord, tailWord_794594, baseEnd_794594] using wordTrace_append hprefix tailTrace_794594
  have hstable : (prefixWord ++ tailWord_794594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794594).length < 2 ^ (prefixWord ++ tailWord_794594).sum := by decide
  have hdescent : baseEnd_794594 < baseStart_794594 := by decide
  rcases family_descends (prefixWord ++ tailWord_794594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794614 : List Nat := [5, 1, 1, 1, 4, 2, 1, 2, 6]
def baseStart_794614 : Nat := 118140960795 + 794614 * 2 ^ 59
def prefixEnd_794614 : Nat := 4983230072969 + 3 ^ 40 * 794614 * 2
def baseEnd_794614 : Nat := 45335435199095478085627

theorem tailTrace_794614 : CollatzResearch.WordTrace tailWord_794614 prefixEnd_794614 45335435199095478085627 := by
  unfold tailWord_794614
  simp only [CollatzResearch.WordTrace]
  refine ⟨1811372096453541381996431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19321302362171108074628597 1811372096453541381996431)
  ·
    refine ⟨2717058144680312072994647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1811372096453541381996431 2717058144680312072994647)
    ·
      refine ⟨4075587217020468109491971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2717058144680312072994647 4075587217020468109491971)
      ·
        refine ⟨6113380825530702164237957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4075587217020468109491971 6113380825530702164237957)
        ·
          refine ⟨1146258904787006655794617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6113380825530702164237957 1146258904787006655794617)
          ·
            refine ⟨859694178590254991845963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1146258904787006655794617 859694178590254991845963)
            ·
              refine ⟨1289541267885382487768945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 859694178590254991845963 1289541267885382487768945)
              ·
                refine ⟨967155950914036865826709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1289541267885382487768945 967155950914036865826709)
                ·
                  refine ⟨45335435199095478085627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 967155950914036865826709 45335435199095478085627)
                  ·
                    rfl

theorem cell23_794614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 2, 6].length) (baseStart_794614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794614 prefixEnd_794614 := by exact prefixLift 794614
  have htrace : WordTrace (prefixWord ++ tailWord_794614) baseStart_794614 baseEnd_794614 := by
    simpa [prefixWord, tailWord_794614, baseEnd_794614] using wordTrace_append hprefix tailTrace_794614
  have hstable : (prefixWord ++ tailWord_794614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794614).length < 2 ^ (prefixWord ++ tailWord_794614).sum := by decide
  have hdescent : baseEnd_794614 < baseStart_794614 := by decide
  rcases family_descends (prefixWord ++ tailWord_794614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794623 : List Nat := [1, 1, 2, 2, 1, 2, 1, 4, 3, 6]
def baseStart_794623 : Nat := 118140960795 + 794623 * 2 ^ 59
def prefixEnd_794623 : Nat := 4983230072969 + 3 ^ 40 * 794623 * 2
def baseEnd_794623 : Nat := 136007846039249922519367

theorem tailTrace_794623 : CollatzResearch.WordTrace tailWord_794623 prefixEnd_794623 136007846039249922519367 := by
  unfold tailWord_794623
  simp only [CollatzResearch.WordTrace]
  refine ⟨28982281800224056649020523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19321521200149371099347015 28982281800224056649020523)
  ·
    refine ⟨43473422700336084973530785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28982281800224056649020523 43473422700336084973530785)
    ·
      refine ⟨32605067025252063730148089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43473422700336084973530785 32605067025252063730148089)
      ·
        refine ⟨24453800268939047797611067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32605067025252063730148089 24453800268939047797611067)
        ·
          refine ⟨36680700403408571696416601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24453800268939047797611067 36680700403408571696416601)
          ·
            refine ⟨27510525302556428772312451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36680700403408571696416601 27510525302556428772312451)
            ·
              refine ⟨41265787953834643158468677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27510525302556428772312451 41265787953834643158468677)
              ·
                refine ⟨7737335241343995592212877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41265787953834643158468677 7737335241343995592212877)
                ·
                  refine ⟨2901500715503998347079829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7737335241343995592212877 2901500715503998347079829)
                  ·
                    refine ⟨136007846039249922519367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2901500715503998347079829 136007846039249922519367)
                    ·
                      rfl

theorem cell23_794623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 3, 6].length) (baseStart_794623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794623 prefixEnd_794623 := by exact prefixLift 794623
  have htrace : WordTrace (prefixWord ++ tailWord_794623) baseStart_794623 baseEnd_794623 := by
    simpa [prefixWord, tailWord_794623, baseEnd_794623] using wordTrace_append hprefix tailTrace_794623
  have hstable : (prefixWord ++ tailWord_794623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794623).length < 2 ^ (prefixWord ++ tailWord_794623).sum := by decide
  have hdescent : baseEnd_794623 < baseStart_794623 := by decide
  rcases family_descends (prefixWord ++ tailWord_794623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794670 : List Nat := [4, 1, 3, 1, 1, 2, 11]
def baseStart_794670 : Nat := 118140960795 + 794670 * 2 ^ 59
def prefixEnd_794670 : Nat := 4983230072969 + 3 ^ 40 * 794670 * 2
def baseEnd_794670 : Nat := 5037625576648284983585

theorem tailTrace_794670 : CollatzResearch.WordTrace tailWord_794670 prefixEnd_794670 5037625576648284983585 := by
  unfold tailWord_794670
  simp only [CollatzResearch.WordTrace]
  refine ⟨3622999503881722959497683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19322664020702522450654309 3622999503881722959497683)
  ·
    refine ⟨5434499255822584439246525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3622999503881722959497683 5434499255822584439246525)
    ·
      refine ⟨2037937220933469164717447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5434499255822584439246525 2037937220933469164717447)
      ·
        refine ⟨3056905831400203747076171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2037937220933469164717447 3056905831400203747076171)
        ·
          refine ⟨4585358747100305620614257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3056905831400203747076171 4585358747100305620614257)
          ·
            refine ⟨3439019060325229215460693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4585358747100305620614257 3439019060325229215460693)
            ·
              refine ⟨5037625576648284983585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 3439019060325229215460693 5037625576648284983585)
              ·
                rfl

theorem cell23_794670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 11].length) (baseStart_794670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794670 prefixEnd_794670 := by exact prefixLift 794670
  have htrace : WordTrace (prefixWord ++ tailWord_794670) baseStart_794670 baseEnd_794670 := by
    simpa [prefixWord, tailWord_794670, baseEnd_794670] using wordTrace_append hprefix tailTrace_794670
  have hstable : (prefixWord ++ tailWord_794670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794670).length < 2 ^ (prefixWord ++ tailWord_794670).sum := by decide
  have hdescent : baseEnd_794670 < baseStart_794670 := by decide
  rcases family_descends (prefixWord ++ tailWord_794670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794683 : List Nat := [1, 1, 1, 1, 1, 2, 1, 5, 1, 9]
def baseStart_794683 : Nat := 118140960795 + 794683 * 2 ^ 59
def prefixEnd_794683 : Nat := 4983230072969 + 3 ^ 40 * 794683 * 2
def baseEnd_794683 : Nat := 136018115652339844269275

theorem tailTrace_794683 : CollatzResearch.WordTrace tailWord_794683 prefixEnd_794683 136018115652339844269275 := by
  unfold tailWord_794683
  simp only [CollatzResearch.WordTrace]
  refine ⟨28984470180006686896204703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19322980120004457930803135 28984470180006686896204703)
  ·
    refine ⟨43476705270010030344307055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28984470180006686896204703 43476705270010030344307055)
    ·
      refine ⟨65215057905015045516460583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43476705270010030344307055 65215057905015045516460583)
      ·
        refine ⟨97822586857522568274690875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65215057905015045516460583 97822586857522568274690875)
        ·
          refine ⟨146733880286283852412036313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97822586857522568274690875 146733880286283852412036313)
          ·
            refine ⟨110050410214712889309027235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146733880286283852412036313 110050410214712889309027235)
            ·
              refine ⟨165075615322069333963540853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110050410214712889309027235 165075615322069333963540853)
              ·
                refine ⟨15475838936444000059081955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 165075615322069333963540853 15475838936444000059081955)
                ·
                  refine ⟨23213758404666000088622933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15475838936444000059081955 23213758404666000088622933)
                  ·
                    refine ⟨136018115652339844269275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 23213758404666000088622933 136018115652339844269275)
                    ·
                      rfl

theorem cell23_794683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 9].length) (baseStart_794683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794683 prefixEnd_794683 := by exact prefixLift 794683
  have htrace : WordTrace (prefixWord ++ tailWord_794683) baseStart_794683 baseEnd_794683 := by
    simpa [prefixWord, tailWord_794683, baseEnd_794683] using wordTrace_append hprefix tailTrace_794683
  have hstable : (prefixWord ++ tailWord_794683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794683).length < 2 ^ (prefixWord ++ tailWord_794683).sum := by decide
  have hdescent : baseEnd_794683 < baseStart_794683 := by decide
  rcases family_descends (prefixWord ++ tailWord_794683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794694 : List Nat := [6, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4]
def baseStart_794694 : Nat := 118140960795 + 794694 * 2 ^ 59
def prefixEnd_794694 : Nat := 4983230072969 + 3 ^ 40 * 794694 * 2
def baseEnd_794694 : Nat := 408059995244218989770275

theorem tailTrace_794694 : CollatzResearch.WordTrace tailWord_794694 prefixEnd_794694 408059995244218989770275 := by
  unfold tailWord_794694
  simp only [CollatzResearch.WordTrace]
  refine ⟨905777230717713617964223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19323247588644557183236757 905777230717713617964223)
  ·
    refine ⟨1358665846076570426946335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 905777230717713617964223 1358665846076570426946335)
    ·
      refine ⟨2037998769114855640419503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1358665846076570426946335 2037998769114855640419503)
      ·
        refine ⟨3056998153672283460629255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2037998769114855640419503 3056998153672283460629255)
        ·
          refine ⟨4585497230508425190943883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3056998153672283460629255 4585497230508425190943883)
          ·
            refine ⟨6878245845762637786415825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4585497230508425190943883 6878245845762637786415825)
            ·
              refine ⟨5158684384321978339811869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6878245845762637786415825 5158684384321978339811869)
              ·
                refine ⟨1934506644120741877429451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5158684384321978339811869 1934506644120741877429451)
                ·
                  refine ⟨2901759966181112816144177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1934506644120741877429451 2901759966181112816144177)
                  ·
                    refine ⟨2176319974635834612108133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2901759966181112816144177 2176319974635834612108133)
                    ·
                      refine ⟨408059995244218989770275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2176319974635834612108133 408059995244218989770275)
                      ·
                        rfl

theorem cell23_794694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_794694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794694 prefixEnd_794694 := by exact prefixLift 794694
  have htrace : WordTrace (prefixWord ++ tailWord_794694) baseStart_794694 baseEnd_794694 := by
    simpa [prefixWord, tailWord_794694, baseEnd_794694] using wordTrace_append hprefix tailTrace_794694
  have hstable : (prefixWord ++ tailWord_794694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794694).length < 2 ^ (prefixWord ++ tailWord_794694).sum := by decide
  have hdescent : baseEnd_794694 < baseStart_794694 := by decide
  rcases family_descends (prefixWord ++ tailWord_794694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794718 : List Nat := [4, 4, 1, 1, 2, 2, 1, 1, 1, 1, 5]
def baseStart_794718 : Nat := 118140960795 + 794718 * 2 ^ 59
def prefixEnd_794718 : Nat := 4983230072969 + 3 ^ 40 * 794718 * 2
def baseEnd_794718 : Nat := 408072318779926895870165

theorem tailTrace_794718 : CollatzResearch.WordTrace tailWord_794718 prefixEnd_794718 408072318779926895870165 := by
  unfold tailWord_794718
  simp only [CollatzResearch.WordTrace]
  refine ⟨3623218341859985984216101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19323831156586591915819205 3623218341859985984216101)
  ·
    refine ⟨679353439098747372040519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3623218341859985984216101 679353439098747372040519)
    ·
      refine ⟨1019030158648121058060779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 679353439098747372040519 1019030158648121058060779)
      ·
        refine ⟨1528545237972181587091169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1019030158648121058060779 1528545237972181587091169)
        ·
          refine ⟨1146408928479136190318377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1528545237972181587091169 1146408928479136190318377)
          ·
            refine ⟨859806696359352142738783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1146408928479136190318377 859806696359352142738783)
            ·
              refine ⟨1289710044539028214108175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 859806696359352142738783 1289710044539028214108175)
              ·
                refine ⟨1934565066808542321162263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1289710044539028214108175 1934565066808542321162263)
                ·
                  refine ⟨2901847600212813481743395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1934565066808542321162263 2901847600212813481743395)
                  ·
                    refine ⟨4352771400319220222615093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2901847600212813481743395 4352771400319220222615093)
                    ·
                      refine ⟨408072318779926895870165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4352771400319220222615093 408072318779926895870165)
                      ·
                        rfl

theorem cell23_794718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_794718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794718 prefixEnd_794718 := by exact prefixLift 794718
  have htrace : WordTrace (prefixWord ++ tailWord_794718) baseStart_794718 baseEnd_794718 := by
    simpa [prefixWord, tailWord_794718, baseEnd_794718] using wordTrace_append hprefix tailTrace_794718
  have hstable : (prefixWord ++ tailWord_794718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794718).length < 2 ^ (prefixWord ++ tailWord_794718).sum := by decide
  have hdescent : baseEnd_794718 < baseStart_794718 := by decide
  rcases family_descends (prefixWord ++ tailWord_794718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794724 : List Nat := [2, 3, 1, 1, 2, 1, 2, 5, 1, 3, 2]
def baseStart_794724 : Nat := 118140960795 + 794724 * 2 ^ 59
def prefixEnd_794724 : Nat := 4983230072969 + 3 ^ 40 * 794724 * 2
def baseEnd_794724 : Nat := 408075399663853872395137

theorem tailTrace_794724 : CollatzResearch.WordTrace tailWord_794724 prefixEnd_794724 408075399663853872395137 := by
  unfold tailWord_794724
  simp only [CollatzResearch.WordTrace]
  refine ⟨14492982786429075449223613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19323977048572100598964817 14492982786429075449223613)
  ·
    refine ⟨5434868544910903293458855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14492982786429075449223613 5434868544910903293458855)
    ·
      refine ⟨8152302817366354940188283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5434868544910903293458855 8152302817366354940188283)
      ·
        refine ⟨12228454226049532410282425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8152302817366354940188283 12228454226049532410282425)
        ·
          refine ⟨9171340669537149307711819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12228454226049532410282425 9171340669537149307711819)
          ·
            refine ⟨13757011004305723961567729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9171340669537149307711819 13757011004305723961567729)
            ·
              refine ⟨10317758253229292971175797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13757011004305723961567729 10317758253229292971175797)
              ·
                refine ⟨967289836240246216047731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10317758253229292971175797 967289836240246216047731)
                ·
                  refine ⟨1450934754360369324071597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 967289836240246216047731 1450934754360369324071597)
                  ·
                    refine ⟨544100532885138496526849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1450934754360369324071597 544100532885138496526849)
                    ·
                      refine ⟨408075399663853872395137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 544100532885138496526849 408075399663853872395137)
                      ·
                        rfl

theorem cell23_794724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 5, 1, 3, 2].length) (baseStart_794724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794724 prefixEnd_794724 := by exact prefixLift 794724
  have htrace : WordTrace (prefixWord ++ tailWord_794724) baseStart_794724 baseEnd_794724 := by
    simpa [prefixWord, tailWord_794724, baseEnd_794724] using wordTrace_append hprefix tailTrace_794724
  have hstable : (prefixWord ++ tailWord_794724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794724).length < 2 ^ (prefixWord ++ tailWord_794724).sum := by decide
  have hdescent : baseEnd_794724 < baseStart_794724 := by decide
  rcases family_descends (prefixWord ++ tailWord_794724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794737 : List Nat := [1, 2, 2, 2, 1, 1, 3, 2, 3, 4, 2]
def baseStart_794737 : Nat := 118140960795 + 794737 * 2 ^ 59
def prefixEnd_794737 : Nat := 4983230072969 + 3 ^ 40 * 794737 * 2
def baseEnd_794737 : Nat := 408082074912362321532577

theorem tailTrace_794737 : CollatzResearch.WordTrace tailWord_794737 prefixEnd_794737 408082074912362321532577 := by
  unfold tailWord_794737
  simp only [CollatzResearch.WordTrace]
  refine ⟨28986439721811054118670465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19324293147874036079113643 28986439721811054118670465)
  ·
    refine ⟨21739829791358290589002849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28986439721811054118670465 21739829791358290589002849)
    ·
      refine ⟨16304872343518717941752137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21739829791358290589002849 16304872343518717941752137)
      ·
        refine ⟨12228654257639038456314103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16304872343518717941752137 12228654257639038456314103)
        ·
          refine ⟨18342981386458557684471155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12228654257639038456314103 18342981386458557684471155)
          ·
            refine ⟨27514472079687836526706733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18342981386458557684471155 27514472079687836526706733)
            ·
              refine ⟨10317927029882938697515025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27514472079687836526706733 10317927029882938697515025)
              ·
                refine ⟨7738445272412204023136269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10317927029882938697515025 7738445272412204023136269)
                ·
                  refine ⟨2901916977154576508676101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7738445272412204023136269 2901916977154576508676101)
                  ·
                    refine ⟨544109433216483095376769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2901916977154576508676101 544109433216483095376769)
                    ·
                      refine ⟨408082074912362321532577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 544109433216483095376769 408082074912362321532577)
                      ·
                        rfl

theorem cell23_794737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 3, 4, 2].length) (baseStart_794737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794737 prefixEnd_794737 := by exact prefixLift 794737
  have htrace : WordTrace (prefixWord ++ tailWord_794737) baseStart_794737 baseEnd_794737 := by
    simpa [prefixWord, tailWord_794737, baseEnd_794737] using wordTrace_append hprefix tailTrace_794737
  have hstable : (prefixWord ++ tailWord_794737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794737).length < 2 ^ (prefixWord ++ tailWord_794737).sum := by decide
  have hdescent : baseEnd_794737 < baseStart_794737 := by decide
  rcases family_descends (prefixWord ++ tailWord_794737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794775 : List Nat := [1, 1, 3, 3, 5, 1, 2, 1, 1, 3, 2]
def baseStart_794775 : Nat := 118140960795 + 794775 * 2 ^ 59
def prefixEnd_794775 : Nat := 4983230072969 + 3 ^ 40 * 794775 * 2
def baseEnd_794775 : Nat := 408101587177233172857403

theorem tailTrace_794775 : CollatzResearch.WordTrace tailWord_794775 prefixEnd_794775 408101587177233172857403 := by
  unfold tailWord_794775
  simp only [CollatzResearch.WordTrace]
  refine ⟨28987825695673386608553779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19325217130448924405702519 28987825695673386608553779)
  ·
    refine ⟨43481738543510079912830669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28987825695673386608553779 43481738543510079912830669)
    ·
      refine ⟨16305651953816279967311501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43481738543510079912830669 16305651953816279967311501)
      ·
        refine ⟨6114619482681104987741813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16305651953816279967311501 6114619482681104987741813)
        ·
          refine ⟨573245576501353592600795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6114619482681104987741813 573245576501353592600795)
          ·
            refine ⟨859868364752030388901193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 573245576501353592600795 859868364752030388901193)
            ·
              refine ⟨644901273564022791675895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 859868364752030388901193 644901273564022791675895)
              ·
                refine ⟨967351910346034187513843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 644901273564022791675895 967351910346034187513843)
                ·
                  refine ⟨1451027865519051281270765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 967351910346034187513843 1451027865519051281270765)
                  ·
                    refine ⟨544135449569644230476537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1451027865519051281270765 544135449569644230476537)
                    ·
                      refine ⟨408101587177233172857403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 544135449569644230476537 408101587177233172857403)
                      ·
                        rfl

theorem cell23_794775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 2, 1, 1, 3, 2].length) (baseStart_794775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794775 prefixEnd_794775 := by exact prefixLift 794775
  have htrace : WordTrace (prefixWord ++ tailWord_794775) baseStart_794775 baseEnd_794775 := by
    simpa [prefixWord, tailWord_794775, baseEnd_794775] using wordTrace_append hprefix tailTrace_794775
  have hstable : (prefixWord ++ tailWord_794775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794775).length < 2 ^ (prefixWord ++ tailWord_794775).sum := by decide
  have hdescent : baseEnd_794775 < baseStart_794775 := by decide
  rcases family_descends (prefixWord ++ tailWord_794775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794805 : List Nat := [1, 3, 3, 4, 2, 1, 1, 1, 1, 4, 2]
def baseStart_794805 : Nat := 118140960795 + 794805 * 2 ^ 59
def prefixEnd_794805 : Nat := 4983230072969 + 3 ^ 40 * 794805 * 2
def baseEnd_794805 : Nat := 408116991596868055482265

theorem tailTrace_794805 : CollatzResearch.WordTrace tailWord_794805 prefixEnd_794805 408116991596868055482265 := by
  unfold tailWord_794805
  simp only [CollatzResearch.WordTrace]
  refine ⟨28988919885564701732145869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19325946590376467821430579 28988919885564701732145869)
  ·
    refine ⟨10870844957086763149554701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28988919885564701732145869 10870844957086763149554701)
    ·
      refine ⟨4076566858907536181083013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10870844957086763149554701 4076566858907536181083013)
      ·
        refine ⟨764356286045163033953065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4076566858907536181083013 764356286045163033953065)
        ·
          refine ⟨573267214533872275464799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 764356286045163033953065 573267214533872275464799)
          ·
            refine ⟨859900821800808413197199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 573267214533872275464799 859900821800808413197199)
            ·
              refine ⟨1289851232701212619795799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 859900821800808413197199 1289851232701212619795799)
              ·
                refine ⟨1934776849051818929693699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1289851232701212619795799 1934776849051818929693699)
                ·
                  refine ⟨2902165273577728394540549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1934776849051818929693699 2902165273577728394540549)
                  ·
                    refine ⟨544155988795824073976353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2902165273577728394540549 544155988795824073976353)
                    ·
                      refine ⟨408116991596868055482265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 544155988795824073976353 408116991596868055482265)
                      ·
                        rfl

theorem cell23_794805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_794805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794805 prefixEnd_794805 := by exact prefixLift 794805
  have htrace : WordTrace (prefixWord ++ tailWord_794805) baseStart_794805 baseEnd_794805 := by
    simpa [prefixWord, tailWord_794805, baseEnd_794805] using wordTrace_append hprefix tailTrace_794805
  have hstable : (prefixWord ++ tailWord_794805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794805).length < 2 ^ (prefixWord ++ tailWord_794805).sum := by decide
  have hdescent : baseEnd_794805 < baseStart_794805 := by decide
  rcases family_descends (prefixWord ++ tailWord_794805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794827 : List Nat := [1, 1, 1, 1, 3, 2, 4, 3, 2, 1, 4]
def baseStart_794827 : Nat := 118140960795 + 794827 * 2 ^ 59
def prefixEnd_794827 : Nat := 4983230072969 + 3 ^ 40 * 794827 * 2
def baseEnd_794827 : Nat := 408128288171266969407163

theorem tailTrace_794827 : CollatzResearch.WordTrace tailWord_794827 prefixEnd_794827 408128288171266969407163 := by
  unfold tailWord_794827
  simp only [CollatzResearch.WordTrace]
  refine ⟨28989722291484999489446735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19326481527656666326297823 28989722291484999489446735)
  ·
    refine ⟨43484583437227499234170103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28989722291484999489446735 43484583437227499234170103)
    ·
      refine ⟨65226875155841248851255155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43484583437227499234170103 65226875155841248851255155)
      ·
        refine ⟨97840312733761873276882733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65226875155841248851255155 97840312733761873276882733)
        ·
          refine ⟨36690117275160702478831025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97840312733761873276882733 36690117275160702478831025)
          ·
            refine ⟨27517587956370526859123269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36690117275160702478831025 27517587956370526859123269)
            ·
              refine ⟨5159547741819473786085613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27517587956370526859123269 5159547741819473786085613)
              ·
                refine ⟨1934830403182302669782105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5159547741819473786085613 1934830403182302669782105)
                ·
                  refine ⟨1451122802386727002336579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1934830403182302669782105 1451122802386727002336579)
                  ·
                    refine ⟨2176684203580090503504869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1451122802386727002336579 2176684203580090503504869)
                    ·
                      refine ⟨408128288171266969407163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2176684203580090503504869 408128288171266969407163)
                      ·
                        rfl

theorem cell23_794827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 3, 2, 1, 4].length) (baseStart_794827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794827 prefixEnd_794827 := by exact prefixLift 794827
  have htrace : WordTrace (prefixWord ++ tailWord_794827) baseStart_794827 baseEnd_794827 := by
    simpa [prefixWord, tailWord_794827, baseEnd_794827] using wordTrace_append hprefix tailTrace_794827
  have hstable : (prefixWord ++ tailWord_794827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794827).length < 2 ^ (prefixWord ++ tailWord_794827).sum := by decide
  have hdescent : baseEnd_794827 < baseStart_794827 := by decide
  rcases family_descends (prefixWord ++ tailWord_794827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794828 : List Nat := [2, 2, 1, 6, 1, 2, 1, 3, 5]
def baseStart_794828 : Nat := 118140960795 + 794828 * 2 ^ 59
def prefixEnd_794828 : Nat := 4983230072969 + 3 ^ 40 * 794828 * 2
def baseEnd_794828 : Nat := 45347644627991273943851

theorem tailTrace_794828 : CollatzResearch.WordTrace tailWord_794828 prefixEnd_794828 45347644627991273943851 := by
  unfold tailWord_794828
  simp only [CollatzResearch.WordTrace]
  refine ⟨14494879382240688330116569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19326505842987584440155425 14494879382240688330116569)
  ·
    refine ⟨10871159536680516247587427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14494879382240688330116569 10871159536680516247587427)
    ·
      refine ⟨16306739305020774371381141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10871159536680516247587427 16306739305020774371381141)
      ·
        refine ⟨764378404922848798658491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 16306739305020774371381141 764378404922848798658491)
        ·
          refine ⟨1146567607384273197987737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 764378404922848798658491 1146567607384273197987737)
          ·
            refine ⟨859925705538204898490803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1146567607384273197987737 859925705538204898490803)
            ·
              refine ⟨1289888558307307347736205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 859925705538204898490803 1289888558307307347736205)
              ·
                refine ⟨483708209365240255401077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1289888558307307347736205 483708209365240255401077)
                ·
                  refine ⟨45347644627991273943851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 483708209365240255401077 45347644627991273943851)
                  ·
                    rfl

theorem cell23_794828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 3, 5].length) (baseStart_794828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794828 prefixEnd_794828 := by exact prefixLift 794828
  have htrace : WordTrace (prefixWord ++ tailWord_794828) baseStart_794828 baseEnd_794828 := by
    simpa [prefixWord, tailWord_794828, baseEnd_794828] using wordTrace_append hprefix tailTrace_794828
  have hstable : (prefixWord ++ tailWord_794828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794828).length < 2 ^ (prefixWord ++ tailWord_794828).sum := by decide
  have hdescent : baseEnd_794828 < baseStart_794828 := by decide
  rcases family_descends (prefixWord ++ tailWord_794828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794867 : List Nat := [1, 1, 1, 2, 2, 4, 3, 3, 6]
def baseStart_794867 : Nat := 118140960795 + 794867 * 2 ^ 59
def prefixEnd_794867 : Nat := 4983230072969 + 3 ^ 40 * 794867 * 2
def baseEnd_794867 : Nat := 45349869710827423656331

theorem tailTrace_794867 : CollatzResearch.WordTrace tailWord_794867 prefixEnd_794867 45349869710827423656331 := by
  unfold tailWord_794867
  simp only [CollatzResearch.WordTrace]
  refine ⟨28991181211340086320902855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19327454140893390880601903 28991181211340086320902855)
  ·
    refine ⟨43486771817010129481354283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28991181211340086320902855 43486771817010129481354283)
    ·
      refine ⟨65230157725515194222031425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43486771817010129481354283 65230157725515194222031425)
      ·
        refine ⟨48922618294136395666523569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65230157725515194222031425 48922618294136395666523569)
        ·
          refine ⟨36691963720602296749892677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48922618294136395666523569 36691963720602296749892677)
          ·
            refine ⟨6879743197612930640604877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36691963720602296749892677 6879743197612930640604877)
            ·
              refine ⟨2579903699104848990226829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6879743197612930640604877 2579903699104848990226829)
              ·
                refine ⟨967463887164318371335061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2579903699104848990226829 967463887164318371335061)
                ·
                  refine ⟨45349869710827423656331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 967463887164318371335061 45349869710827423656331)
                  ·
                    rfl

theorem cell23_794867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 3, 6].length) (baseStart_794867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794867 prefixEnd_794867 := by exact prefixLift 794867
  have htrace : WordTrace (prefixWord ++ tailWord_794867) baseStart_794867 baseEnd_794867 := by
    simpa [prefixWord, tailWord_794867, baseEnd_794867] using wordTrace_append hprefix tailTrace_794867
  have hstable : (prefixWord ++ tailWord_794867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794867).length < 2 ^ (prefixWord ++ tailWord_794867).sum := by decide
  have hdescent : baseEnd_794867 < baseStart_794867 := by decide
  rcases family_descends (prefixWord ++ tailWord_794867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794877 : List Nat := [1, 4, 1, 1, 1, 1, 1, 3, 2, 5, 3]
def baseStart_794877 : Nat := 118140960795 + 794877 * 2 ^ 59
def prefixEnd_794877 : Nat := 4983230072969 + 3 ^ 40 * 794877 * 2
def baseEnd_794877 : Nat := 408153962203991773781933

theorem tailTrace_794877 : CollatzResearch.WordTrace tailWord_794877 prefixEnd_794877 408153962203991773781933 := by
  unfold tailWord_794877
  simp only [CollatzResearch.WordTrace]
  refine ⟨28991545941303858028766885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19327697294202572019177923 28991545941303858028766885)
  ·
    refine ⟨5435914863994473380393791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28991545941303858028766885 5435914863994473380393791)
    ·
      refine ⟨8153872295991710070590687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5435914863994473380393791 8153872295991710070590687)
      ·
        refine ⟨12230808443987565105886031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8153872295991710070590687 12230808443987565105886031)
        ·
          refine ⟨18346212665981347658829047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12230808443987565105886031 18346212665981347658829047)
          ·
            refine ⟨27519318998972021488243571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18346212665981347658829047 27519318998972021488243571)
            ·
              refine ⟨41278978498458032232365357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27519318998972021488243571 41278978498458032232365357)
              ·
                refine ⟨15479616936921762087137009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41278978498458032232365357 15479616936921762087137009)
                ·
                  refine ⟨11609712702691321565352757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15479616936921762087137009 11609712702691321565352757)
                  ·
                    refine ⟨1088410565877311396751821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11609712702691321565352757 1088410565877311396751821)
                    ·
                      refine ⟨408153962203991773781933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1088410565877311396751821 408153962203991773781933)
                      ·
                        rfl

theorem cell23_794877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 5, 3].length) (baseStart_794877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794877 prefixEnd_794877 := by exact prefixLift 794877
  have htrace : WordTrace (prefixWord ++ tailWord_794877) baseStart_794877 baseEnd_794877 := by
    simpa [prefixWord, tailWord_794877, baseEnd_794877] using wordTrace_append hprefix tailTrace_794877
  have hstable : (prefixWord ++ tailWord_794877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794877).length < 2 ^ (prefixWord ++ tailWord_794877).sum := by decide
  have hdescent : baseEnd_794877 < baseStart_794877 := by decide
  rcases family_descends (prefixWord ++ tailWord_794877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794914 : List Nat := [3, 3, 1, 1, 3, 1, 1, 2, 3, 5]
def baseStart_794914 : Nat := 118140960795 + 794914 * 2 ^ 59
def prefixEnd_794914 : Nat := 4983230072969 + 3 ^ 40 * 794914 * 2
def baseEnd_794914 : Nat := 136057653662736043006421

theorem tailTrace_794914 : CollatzResearch.WordTrace tailWord_794914 prefixEnd_794914 136057653662736043006421 := by
  unfold tailWord_794914
  simp only [CollatzResearch.WordTrace]
  refine ⟨7248223860542453336965949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19328596961446542231909197 7248223860542453336965949)
  ·
    refine ⟨2718083947703420001362231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7248223860542453336965949 2718083947703420001362231)
    ·
      refine ⟨4077125921555130002043347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2718083947703420001362231 4077125921555130002043347)
      ·
        refine ⟨6115688882332695003065021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4077125921555130002043347 6115688882332695003065021)
        ·
          refine ⟨2293383330874760626149383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6115688882332695003065021 2293383330874760626149383)
          ·
            refine ⟨3440074996312140939224075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2293383330874760626149383 3440074996312140939224075)
            ·
              refine ⟨5160112494468211408836113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3440074996312140939224075 5160112494468211408836113)
              ·
                refine ⟨3870084370851158556627085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5160112494468211408836113 3870084370851158556627085)
                ·
                  refine ⟨1451281639069184458735157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3870084370851158556627085 1451281639069184458735157)
                  ·
                    refine ⟨136057653662736043006421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1451281639069184458735157 136057653662736043006421)
                    ·
                      rfl

theorem cell23_794914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_794914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794914 prefixEnd_794914 := by exact prefixLift 794914
  have htrace : WordTrace (prefixWord ++ tailWord_794914) baseStart_794914 baseEnd_794914 := by
    simpa [prefixWord, tailWord_794914, baseEnd_794914] using wordTrace_append hprefix tailTrace_794914
  have hstable : (prefixWord ++ tailWord_794914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794914).length < 2 ^ (prefixWord ++ tailWord_794914).sum := by decide
  have hdescent : baseEnd_794914 < baseStart_794914 := by decide
  rcases family_descends (prefixWord ++ tailWord_794914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794927 : List Nat := [1, 1, 2, 1, 2, 1, 5, 3, 1, 6]
def baseStart_794927 : Nat := 118140960795 + 794927 * 2 ^ 59
def prefixEnd_794927 : Nat := 4983230072969 + 3 ^ 40 * 794927 * 2
def baseEnd_794927 : Nat := 136059878745572192718901

theorem tailTrace_794927 : CollatzResearch.WordTrace tailWord_794927 prefixEnd_794927 136059878745572192718901 := by
  unfold tailWord_794927
  simp only [CollatzResearch.WordTrace]
  refine ⟨28993369591122716568087035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19328913060748477712058023 28993369591122716568087035)
  ·
    refine ⟨43490054386684074852130553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28993369591122716568087035 43490054386684074852130553)
    ·
      refine ⟨32617540790013056139097915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43490054386684074852130553 32617540790013056139097915)
      ·
        refine ⟨48926311185019584208646873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32617540790013056139097915 48926311185019584208646873)
        ·
          refine ⟨36694733388764688156485155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48926311185019584208646873 36694733388764688156485155)
          ·
            refine ⟨55042100083147032234727733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36694733388764688156485155 55042100083147032234727733)
            ·
              refine ⟨5160196882795034272005725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55042100083147032234727733 5160196882795034272005725)
              ·
                refine ⟨1935073831048137852002147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5160196882795034272005725 1935073831048137852002147)
                ·
                  refine ⟨2902610746572206778003221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1935073831048137852002147 2902610746572206778003221)
                  ·
                    refine ⟨136059878745572192718901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2902610746572206778003221 136059878745572192718901)
                    ·
                      rfl

theorem cell23_794927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 3, 1, 6].length) (baseStart_794927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794927 prefixEnd_794927 := by exact prefixLift 794927
  have htrace : WordTrace (prefixWord ++ tailWord_794927) baseStart_794927 baseEnd_794927 := by
    simpa [prefixWord, tailWord_794927, baseEnd_794927] using wordTrace_append hprefix tailTrace_794927
  have hstable : (prefixWord ++ tailWord_794927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794927).length < 2 ^ (prefixWord ++ tailWord_794927).sum := by decide
  have hdescent : baseEnd_794927 < baseStart_794927 := by decide
  rcases family_descends (prefixWord ++ tailWord_794927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794938 : List Nat := [3, 1, 1, 1, 4, 4, 1, 1, 2, 3, 2]
def baseStart_794938 : Nat := 118140960795 + 794938 * 2 ^ 59
def prefixEnd_794938 : Nat := 4983230072969 + 3 ^ 40 * 794938 * 2
def baseEnd_794938 : Nat := 408185284523916035119153

theorem tailTrace_794938 : CollatzResearch.WordTrace tailWord_794938 prefixEnd_794938 408185284523916035119153 := by
  unfold tailWord_794938
  simp only [CollatzResearch.WordTrace]
  refine ⟨7248442698520716361684367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19329180529388576964491645 7248442698520716361684367)
  ·
    refine ⟨10872664047781074542526551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7248442698520716361684367 10872664047781074542526551)
    ·
      refine ⟨16308996071671611813789827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10872664047781074542526551 16308996071671611813789827)
      ·
        refine ⟨24463494107507417720684741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16308996071671611813789827 24463494107507417720684741)
        ·
          refine ⟨4586905145157640822628389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24463494107507417720684741 4586905145157640822628389)
          ·
            refine ⟨860044714717057654242823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4586905145157640822628389 860044714717057654242823)
            ·
              refine ⟨1290067072075586481364235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 860044714717057654242823 1290067072075586481364235)
              ·
                refine ⟨1935100608113379722046353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1290067072075586481364235 1935100608113379722046353)
                ·
                  refine ⟨1451325456085034791534765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1935100608113379722046353 1451325456085034791534765)
                  ·
                    refine ⟨544247046031888046825537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1451325456085034791534765 544247046031888046825537)
                    ·
                      refine ⟨408185284523916035119153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 544247046031888046825537 408185284523916035119153)
                      ·
                        rfl

theorem cell23_794938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 1, 2, 3, 2].length) (baseStart_794938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794938 prefixEnd_794938 := by exact prefixLift 794938
  have htrace : WordTrace (prefixWord ++ tailWord_794938) baseStart_794938 baseEnd_794938 := by
    simpa [prefixWord, tailWord_794938, baseEnd_794938] using wordTrace_append hprefix tailTrace_794938
  have hstable : (prefixWord ++ tailWord_794938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794938).length < 2 ^ (prefixWord ++ tailWord_794938).sum := by decide
  have hdescent : baseEnd_794938 < baseStart_794938 := by decide
  rcases family_descends (prefixWord ++ tailWord_794938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794948 : List Nat := [2, 3, 4, 1, 2, 1, 1, 3, 1, 5]
def baseStart_794948 : Nat := 118140960795 + 794948 * 2 ^ 59
def prefixEnd_794948 : Nat := 4983230072969 + 3 ^ 40 * 794948 * 2
def baseEnd_794948 : Nat := 136063473110153665331369

theorem tailTrace_794948 : CollatzResearch.WordTrace tailWord_794948 prefixEnd_794948 136063473110153665331369 := by
  unfold tailWord_794948
  simp only [CollatzResearch.WordTrace]
  refine ⟨14497067762023318577300749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19329423682697758103067665 14497067762023318577300749)
  ·
    refine ⟨5436400410758744466487781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14497067762023318577300749 5436400410758744466487781)
    ·
      refine ⟨1019325077017264587466459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5436400410758744466487781 1019325077017264587466459)
      ·
        refine ⟨1528987615525896881199689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1019325077017264587466459 1528987615525896881199689)
        ·
          refine ⟨1146740711644422660899767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1528987615525896881199689 1146740711644422660899767)
          ·
            refine ⟨1720111067466633991349651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1146740711644422660899767 1720111067466633991349651)
            ·
              refine ⟨2580166601199950987024477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1720111067466633991349651 2580166601199950987024477)
              ·
                refine ⟨967562475449981620134179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2580166601199950987024477 967562475449981620134179)
                ·
                  refine ⟨1451343713174972430201269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 967562475449981620134179 1451343713174972430201269)
                  ·
                    refine ⟨136063473110153665331369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1451343713174972430201269 136063473110153665331369)
                    ·
                      rfl

theorem cell23_794948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_794948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794948 prefixEnd_794948 := by exact prefixLift 794948
  have htrace : WordTrace (prefixWord ++ tailWord_794948) baseStart_794948 baseEnd_794948 := by
    simpa [prefixWord, tailWord_794948, baseEnd_794948] using wordTrace_append hprefix tailTrace_794948
  have hstable : (prefixWord ++ tailWord_794948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794948).length < 2 ^ (prefixWord ++ tailWord_794948).sum := by decide
  have hdescent : baseEnd_794948 < baseStart_794948 := by decide
  rcases family_descends (prefixWord ++ tailWord_794948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794951 : List Nat := [1, 1, 4, 1, 2, 2, 1, 2, 5, 2, 2]
def baseStart_794951 : Nat := 118140960795 + 794951 * 2 ^ 59
def prefixEnd_794951 : Nat := 4983230072969 + 3 ^ 40 * 794951 * 2
def baseEnd_794951 : Nat := 408191959772424484256593

theorem tailTrace_794951 : CollatzResearch.WordTrace tailWord_794951 prefixEnd_794951 408191959772424484256593 := by
  unfold tailWord_794951
  simp only [CollatzResearch.WordTrace]
  refine ⟨28994244943035768666960707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19329496628690512444640471 28994244943035768666960707)
  ·
    refine ⟨43491367414553653000441061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28994244943035768666960707 43491367414553653000441061)
    ·
      refine ⟨8154631390228809937582699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43491367414553653000441061 8154631390228809937582699)
      ·
        refine ⟨12231947085343214906374049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8154631390228809937582699 12231947085343214906374049)
        ·
          refine ⟨9173960314007411179780537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12231947085343214906374049 9173960314007411179780537)
          ·
            refine ⟨6880470235505558384835403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9173960314007411179780537 6880470235505558384835403)
            ·
              refine ⟨10320705353258337577253105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6880470235505558384835403 10320705353258337577253105)
              ·
                refine ⟨7740529014943753182939829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10320705353258337577253105 7740529014943753182939829)
                ·
                  refine ⟨725674595150976860900609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7740529014943753182939829 725674595150976860900609)
                  ·
                    refine ⟨544255946363232645675457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 725674595150976860900609 544255946363232645675457)
                    ·
                      refine ⟨408191959772424484256593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 544255946363232645675457 408191959772424484256593)
                      ·
                        rfl

theorem cell23_794951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 5, 2, 2].length) (baseStart_794951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794951 prefixEnd_794951 := by exact prefixLift 794951
  have htrace : WordTrace (prefixWord ++ tailWord_794951) baseStart_794951 baseEnd_794951 := by
    simpa [prefixWord, tailWord_794951, baseEnd_794951] using wordTrace_append hprefix tailTrace_794951
  have hstable : (prefixWord ++ tailWord_794951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794951).length < 2 ^ (prefixWord ++ tailWord_794951).sum := by decide
  have hdescent : baseEnd_794951 < baseStart_794951 := by decide
  rcases family_descends (prefixWord ++ tailWord_794951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794961 : List Nat := [1, 2, 2, 1, 4, 2, 3, 2, 2, 4]
def baseStart_794961 : Nat := 118140960795 + 794961 * 2 ^ 59
def prefixEnd_794961 : Nat := 4983230072969 + 3 ^ 40 * 794961 * 2
def baseEnd_794961 : Nat := 136065698192989815043849

theorem tailTrace_794961 : CollatzResearch.WordTrace tailWord_794961 prefixEnd_794961 136065698192989815043849 := by
  unfold tailWord_794961
  simp only [CollatzResearch.WordTrace]
  refine ⟨28994609672999540374824737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19329739781999693583216491 28994609672999540374824737)
  ·
    refine ⟨21745957254749655281118553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28994609672999540374824737 21745957254749655281118553)
    ·
      refine ⟨16309467941062241460838915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21745957254749655281118553 16309467941062241460838915)
      ·
        refine ⟨24464201911593362191258373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16309467941062241460838915 24464201911593362191258373)
        ·
          refine ⟨4587037858423755410860945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24464201911593362191258373 4587037858423755410860945)
          ·
            refine ⟨3440278393817816558145709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4587037858423755410860945 3440278393817816558145709)
            ·
              refine ⟨1290104397681681209304641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3440278393817816558145709 1290104397681681209304641)
              ·
                refine ⟨967578298261260906978481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1290104397681681209304641 967578298261260906978481)
                ·
                  refine ⟨725683723695945680233861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 967578298261260906978481 725683723695945680233861)
                  ·
                    refine ⟨136065698192989815043849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 725683723695945680233861 136065698192989815043849)
                    ·
                      rfl

theorem cell23_794961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 2, 2, 4].length) (baseStart_794961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794961 prefixEnd_794961 := by exact prefixLift 794961
  have htrace : WordTrace (prefixWord ++ tailWord_794961) baseStart_794961 baseEnd_794961 := by
    simpa [prefixWord, tailWord_794961, baseEnd_794961] using wordTrace_append hprefix tailTrace_794961
  have hstable : (prefixWord ++ tailWord_794961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794961).length < 2 ^ (prefixWord ++ tailWord_794961).sum := by decide
  have hdescent : baseEnd_794961 < baseStart_794961 := by decide
  rcases family_descends (prefixWord ++ tailWord_794961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794981 : List Nat := [1, 3, 1, 3, 1, 5, 1, 1, 1, 2, 4]
def baseStart_794981 : Nat := 118140960795 + 794981 * 2 ^ 59
def prefixEnd_794981 : Nat := 4983230072969 + 3 ^ 40 * 794981 * 2
def baseEnd_794981 : Nat := 408207364192059366881455

theorem tailTrace_794981 : CollatzResearch.WordTrace tailWord_794981 prefixEnd_794981 408207364192059366881455 := by
  unfold tailWord_794981
  simp only [CollatzResearch.WordTrace]
  refine ⟨28995339132927083790552797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19330226088618055860368531 28995339132927083790552797)
  ·
    refine ⟨10873252174847656421457299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28995339132927083790552797 10873252174847656421457299)
    ·
      refine ⟨16309878262271484632185949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10873252174847656421457299 16309878262271484632185949)
      ·
        refine ⟨6116204348351806737069731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16309878262271484632185949 6116204348351806737069731)
        ·
          refine ⟨9174306522527710105604597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6116204348351806737069731 9174306522527710105604597)
          ·
            refine ⟨860091236486972822400431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9174306522527710105604597 860091236486972822400431)
            ·
              refine ⟨1290136854730459233600647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 860091236486972822400431 1290136854730459233600647)
              ·
                refine ⟨1935205282095688850400971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1290136854730459233600647 1935205282095688850400971)
                ·
                  refine ⟨2902807923143533275601457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1935205282095688850400971 2902807923143533275601457)
                  ·
                    refine ⟨2177105942357649956701093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2902807923143533275601457 2177105942357649956701093)
                    ·
                      refine ⟨408207364192059366881455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2177105942357649956701093 408207364192059366881455)
                      ·
                        rfl

theorem cell23_794981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 1, 1, 2, 4].length) (baseStart_794981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794981 prefixEnd_794981 := by exact prefixLift 794981
  have htrace : WordTrace (prefixWord ++ tailWord_794981) baseStart_794981 baseEnd_794981 := by
    simpa [prefixWord, tailWord_794981, baseEnd_794981] using wordTrace_append hprefix tailTrace_794981
  have hstable : (prefixWord ++ tailWord_794981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794981).length < 2 ^ (prefixWord ++ tailWord_794981).sum := by decide
  have hdescent : baseEnd_794981 < baseStart_794981 := by decide
  rcases family_descends (prefixWord ++ tailWord_794981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794988 : List Nat := [2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 3]
def baseStart_794988 : Nat := 118140960795 + 794988 * 2 ^ 59
def prefixEnd_794988 : Nat := 4983230072969 + 3 ^ 40 * 794988 * 2
def baseEnd_794988 : Nat := 408210958556640839493923

theorem tailTrace_794988 : CollatzResearch.WordTrace tailWord_794988 prefixEnd_794988 408210958556640839493923 := by
  unfold tailWord_794988
  simp only [CollatzResearch.WordTrace]
  refine ⟨14497797221950861993028809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19330396295934482657371745 14497797221950861993028809)
  ·
    refine ⟨10873347916463146494771607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14497797221950861993028809 10873347916463146494771607)
    ·
      refine ⟨16310021874694719742157411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10873347916463146494771607 16310021874694719742157411)
      ·
        refine ⟨24465032812042079613236117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16310021874694719742157411 24465032812042079613236117)
        ·
          refine ⟨1146798413064472481870443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24465032812042079613236117 1146798413064472481870443)
          ·
            refine ⟨1720197619596708722805665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1146798413064472481870443 1720197619596708722805665)
            ·
              refine ⟨1290148214697531542104249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1720197619596708722805665 1290148214697531542104249)
              ·
                refine ⟨967611161023148656578187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1290148214697531542104249 967611161023148656578187)
                ·
                  refine ⟨1451416741534722984867281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 967611161023148656578187 1451416741534722984867281)
                  ·
                    refine ⟨1088562556151042238650461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1451416741534722984867281 1088562556151042238650461)
                    ·
                      refine ⟨408210958556640839493923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1088562556151042238650461 408210958556640839493923)
                      ·
                        rfl

theorem cell23_794988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 3].length) (baseStart_794988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_794988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_794988 prefixEnd_794988 := by exact prefixLift 794988
  have htrace : WordTrace (prefixWord ++ tailWord_794988) baseStart_794988 baseEnd_794988 := by
    simpa [prefixWord, tailWord_794988, baseEnd_794988] using wordTrace_append hprefix tailTrace_794988
  have hstable : (prefixWord ++ tailWord_794988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794988).length < 2 ^ (prefixWord ++ tailWord_794988).sum := by decide
  have hdescent : baseEnd_794988 < baseStart_794988 := by decide
  rcases family_descends (prefixWord ++ tailWord_794988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795044 : List Nat := [2, 3, 1, 2, 1, 1, 3, 2, 2, 1, 5]
def baseStart_795044 : Nat := 118140960795 + 795044 * 2 ^ 59
def prefixEnd_795044 : Nat := 4983230072969 + 3 ^ 40 * 795044 * 2
def baseEnd_795044 : Nat := 408239713473292620393665

theorem tailTrace_795044 : CollatzResearch.WordTrace tailWord_795044 prefixEnd_795044 408239713473292620393665 := by
  unfold tailWord_795044
  simp only [CollatzResearch.WordTrace]
  refine ⟨14498818465849422775048093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19331757954465897033397457 14498818465849422775048093)
  ·
    refine ⟨5437056924693533540643035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14498818465849422775048093 5437056924693533540643035)
    ·
      refine ⟨8155585387040300310964553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5437056924693533540643035 8155585387040300310964553)
      ·
        refine ⟨6116689040280225233223415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8155585387040300310964553 6116689040280225233223415)
        ·
          refine ⟨9175033560420337849835123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6116689040280225233223415 9175033560420337849835123)
          ·
            refine ⟨13762550340630506774752685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9175033560420337849835123 13762550340630506774752685)
            ·
              refine ⟨5160956377736440040532257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13762550340630506774752685 5160956377736440040532257)
              ·
                refine ⟨3870717283302330030399193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5160956377736440040532257 3870717283302330030399193)
                ·
                  refine ⟨2903037962476747522799395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3870717283302330030399193 2903037962476747522799395)
                  ·
                    refine ⟨4354556943715121284199093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2903037962476747522799395 4354556943715121284199093)
                    ·
                      refine ⟨408239713473292620393665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4354556943715121284199093 408239713473292620393665)
                      ·
                        rfl

theorem cell23_795044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_795044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_795044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_795044 prefixEnd_795044 := by exact prefixLift 795044
  have htrace : WordTrace (prefixWord ++ tailWord_795044) baseStart_795044 baseEnd_795044 := by
    simpa [prefixWord, tailWord_795044, baseEnd_795044] using wordTrace_append hprefix tailTrace_795044
  have hstable : (prefixWord ++ tailWord_795044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795044).length < 2 ^ (prefixWord ++ tailWord_795044).sum := by decide
  have hdescent : baseEnd_795044 < baseStart_795044 := by decide
  rcases family_descends (prefixWord ++ tailWord_795044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795141 : List Nat := [1, 3, 1, 1, 2, 2, 3, 3, 3, 4]
def baseStart_795141 : Nat := 118140960795 + 795141 * 2 ^ 59
def prefixEnd_795141 : Nat := 4983230072969 + 3 ^ 40 * 795141 * 2
def baseEnd_795141 : Nat := 136096507032259580293573

theorem tailTrace_795141 : CollatzResearch.WordTrace tailWord_795141 prefixEnd_795141 136096507032259580293573 := by
  unfold tailWord_795141
  simp only [CollatzResearch.WordTrace]
  refine ⟨29001174812347431116377277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19334116541564954077584851 29001174812347431116377277)
  ·
    refine ⟨10875440554630286668641479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29001174812347431116377277 10875440554630286668641479)
    ·
      refine ⟨16313160831945430002962219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10875440554630286668641479 16313160831945430002962219)
      ·
        refine ⟨24469741247918145004443329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16313160831945430002962219 24469741247918145004443329)
        ·
          refine ⟨18352305935938608753332497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24469741247918145004443329 18352305935938608753332497)
          ·
            refine ⟨13764229451953956564999373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18352305935938608753332497 13764229451953956564999373)
            ·
              refine ⟨5161586044482733711874765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13764229451953956564999373 5161586044482733711874765)
              ·
                refine ⟨1935594766681025141953037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5161586044482733711874765 1935594766681025141953037)
                ·
                  refine ⟨725848037505384428232389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1935594766681025141953037 725848037505384428232389)
                  ·
                    refine ⟨136096507032259580293573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 725848037505384428232389 136096507032259580293573)
                    ·
                      rfl

theorem cell23_795141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 3, 3, 4].length) (baseStart_795141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_795141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_795141 prefixEnd_795141 := by exact prefixLift 795141
  have htrace : WordTrace (prefixWord ++ tailWord_795141) baseStart_795141 baseEnd_795141 := by
    simpa [prefixWord, tailWord_795141, baseEnd_795141] using wordTrace_append hprefix tailTrace_795141
  have hstable : (prefixWord ++ tailWord_795141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795141).length < 2 ^ (prefixWord ++ tailWord_795141).sum := by decide
  have hdescent : baseEnd_795141 < baseStart_795141 := by decide
  rcases family_descends (prefixWord ++ tailWord_795141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795142 : List Nat := [6, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3]
def baseStart_795142 : Nat := 118140960795 + 795142 * 2 ^ 59
def prefixEnd_795142 : Nat := 4983230072969 + 3 ^ 40 * 795142 * 2
def baseEnd_795142 : Nat := 408290034577433236968215

theorem tailTrace_795142 : CollatzResearch.WordTrace tailWord_795142 prefixEnd_795142 408290034577433236968215 := by
  unfold tailWord_795142
  simp only [CollatzResearch.WordTrace]
  refine ⟨906287852666994008973865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19334140856895872191442453 906287852666994008973865)
  ·
    refine ⟨679715889500245506730399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 906287852666994008973865 679715889500245506730399)
    ·
      refine ⟨1019573834250368260095599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 679715889500245506730399 1019573834250368260095599)
      ·
        refine ⟨1529360751375552390143399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1019573834250368260095599 1529360751375552390143399)
        ·
          refine ⟨2294041127063328585215099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1529360751375552390143399 2294041127063328585215099)
          ·
            refine ⟨3441061690594992877822649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2294041127063328585215099 3441061690594992877822649)
            ·
              refine ⟨2580796267946244658366987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3441061690594992877822649 2580796267946244658366987)
              ·
                refine ⟨3871194401919366987550481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2580796267946244658366987 3871194401919366987550481)
                ·
                  refine ⟨2903395801439525240662861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3871194401919366987550481 2903395801439525240662861)
                  ·
                    refine ⟨1088773425539821965248573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2903395801439525240662861 1088773425539821965248573)
                    ·
                      refine ⟨408290034577433236968215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1088773425539821965248573 408290034577433236968215)
                      ·
                        rfl

theorem cell23_795142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_795142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_795142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_795142 prefixEnd_795142 := by exact prefixLift 795142
  have htrace : WordTrace (prefixWord ++ tailWord_795142) baseStart_795142 baseEnd_795142 := by
    simpa [prefixWord, tailWord_795142, baseEnd_795142] using wordTrace_append hprefix tailTrace_795142
  have hstable : (prefixWord ++ tailWord_795142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795142).length < 2 ^ (prefixWord ++ tailWord_795142).sum := by decide
  have hdescent : baseEnd_795142 < baseStart_795142 := by decide
  rcases family_descends (prefixWord ++ tailWord_795142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795144 : List Nat := [2, 1, 3, 2, 1, 1, 1, 1, 4, 1, 6]
def baseStart_795144 : Nat := 118140960795 + 795144 * 2 ^ 59
def prefixEnd_795144 : Nat := 4983230072969 + 3 ^ 40 * 795144 * 2
def baseEnd_795144 : Nat := 408291061538742229143205

theorem tailTrace_795144 : CollatzResearch.WordTrace tailWord_795144 prefixEnd_795144 408291061538742229143205 := by
  unfold tailWord_795144
  simp only [CollatzResearch.WordTrace]
  refine ⟨14500642115668281314368243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19334189487557708419157657 14500642115668281314368243)
  ·
    refine ⟨21750963173502421971552365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14500642115668281314368243 21750963173502421971552365)
    ·
      refine ⟨8156611190063408239332137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21750963173502421971552365 8156611190063408239332137)
      ·
        refine ⟨6117458392547556179499103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8156611190063408239332137 6117458392547556179499103)
        ·
          refine ⟨9176187588821334269248655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6117458392547556179499103 9176187588821334269248655)
          ·
            refine ⟨13764281383232001403872983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9176187588821334269248655 13764281383232001403872983)
            ·
              refine ⟨20646422074848002105809475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13764281383232001403872983 20646422074848002105809475)
              ·
                refine ⟨30969633112272003158714213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20646422074848002105809475 30969633112272003158714213)
                ·
                  refine ⟨5806806208551000592258915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30969633112272003158714213 5806806208551000592258915)
                  ·
                    refine ⟨8710209312826500888388373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5806806208551000592258915 8710209312826500888388373)
                    ·
                      refine ⟨408291061538742229143205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8710209312826500888388373 408291061538742229143205)
                      ·
                        rfl

theorem cell23_795144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_795144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_795144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_795144 prefixEnd_795144 := by exact prefixLift 795144
  have htrace : WordTrace (prefixWord ++ tailWord_795144) baseStart_795144 baseEnd_795144 := by
    simpa [prefixWord, tailWord_795144, baseEnd_795144] using wordTrace_append hprefix tailTrace_795144
  have hstable : (prefixWord ++ tailWord_795144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795144).length < 2 ^ (prefixWord ++ tailWord_795144).sum := by decide
  have hdescent : baseEnd_795144 < baseStart_795144 := by decide
  rcases family_descends (prefixWord ++ tailWord_795144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795148 : List Nat := [2, 2, 1, 2, 4, 1, 2, 1, 2, 4, 2]
def baseStart_795148 : Nat := 118140960795 + 795148 * 2 ^ 59
def prefixEnd_795148 : Nat := 4983230072969 + 3 ^ 40 * 795148 * 2
def baseEnd_795148 : Nat := 408293115461360213493187

theorem tailTrace_795148 : CollatzResearch.WordTrace tailWord_795148 prefixEnd_795148 408293115461360213493187 := by
  unfold tailWord_795148
  simp only [CollatzResearch.WordTrace]
  refine ⟨14500715061661035655941049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19334286748881380874588065 14500715061661035655941049)
  ·
    refine ⟨10875536296245776741955787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14500715061661035655941049 10875536296245776741955787)
    ·
      refine ⟨16313304444368665112933681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10875536296245776741955787 16313304444368665112933681)
      ·
        refine ⟨12234978333276498834700261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16313304444368665112933681 12234978333276498834700261)
        ·
          refine ⟨2294058437489343531506299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12234978333276498834700261 2294058437489343531506299)
          ·
            refine ⟨3441087656234015297259449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2294058437489343531506299 3441087656234015297259449)
            ·
              refine ⟨2580815742175511472944587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3441087656234015297259449 2580815742175511472944587)
              ·
                refine ⟨3871223613263267209416881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2580815742175511472944587 3871223613263267209416881)
                ·
                  refine ⟨2903417709947450407062661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3871223613263267209416881 2903417709947450407062661)
                  ·
                    refine ⟨544390820615146951324249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2903417709947450407062661 544390820615146951324249)
                    ·
                      refine ⟨408293115461360213493187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 544390820615146951324249 408293115461360213493187)
                      ·
                        rfl

theorem cell23_795148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 2, 4, 2].length) (baseStart_795148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_795148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_795148 prefixEnd_795148 := by exact prefixLift 795148
  have htrace : WordTrace (prefixWord ++ tailWord_795148) baseStart_795148 baseEnd_795148 := by
    simpa [prefixWord, tailWord_795148, baseEnd_795148] using wordTrace_append hprefix tailTrace_795148
  have hstable : (prefixWord ++ tailWord_795148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795148).length < 2 ^ (prefixWord ++ tailWord_795148).sum := by decide
  have hdescent : baseEnd_795148 < baseStart_795148 := by decide
  rcases family_descends (prefixWord ++ tailWord_795148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795231 : List Nat := [1, 1, 2, 3, 1, 1, 1, 3, 6, 4]
def baseStart_795231 : Nat := 118140960795 + 795231 * 2 ^ 59
def prefixEnd_795231 : Nat := 4983230072969 + 3 ^ 40 * 795231 * 2
def baseEnd_795231 : Nat := 136111911451894462918435

theorem tailTrace_795231 : CollatzResearch.WordTrace tailWord_795231 prefixEnd_795231 136111911451894462918435 := by
  unfold tailWord_795231
  simp only [CollatzResearch.WordTrace]
  refine ⟨29004457382021376487153547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19336304921347584324769031 29004457382021376487153547)
  ·
    refine ⟨43506686073032064730730321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29004457382021376487153547 43506686073032064730730321)
    ·
      refine ⟨32630014554774048548047741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43506686073032064730730321 32630014554774048548047741)
      ·
        refine ⟨12236255458040268205517903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32630014554774048548047741 12236255458040268205517903)
        ·
          refine ⟨18354383187060402308276855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12236255458040268205517903 18354383187060402308276855)
          ·
            refine ⟨27531574780590603462415283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18354383187060402308276855 27531574780590603462415283)
            ·
              refine ⟨41297362170885905193622925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27531574780590603462415283 41297362170885905193622925)
              ·
                refine ⟨15486510814082214447608597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41297362170885905193622925 15486510814082214447608597)
                ·
                  refine ⟨725930194410103802231653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 15486510814082214447608597 725930194410103802231653)
                  ·
                    refine ⟨136111911451894462918435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 725930194410103802231653 136111911451894462918435)
                    ·
                      rfl

theorem cell23_795231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 6, 4].length) (baseStart_795231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_795231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_795231 prefixEnd_795231 := by exact prefixLift 795231
  have htrace : WordTrace (prefixWord ++ tailWord_795231) baseStart_795231 baseEnd_795231 := by
    simpa [prefixWord, tailWord_795231, baseEnd_795231] using wordTrace_append hprefix tailTrace_795231
  have hstable : (prefixWord ++ tailWord_795231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795231).length < 2 ^ (prefixWord ++ tailWord_795231).sum := by decide
  have hdescent : baseEnd_795231 < baseStart_795231 := by decide
  rcases family_descends (prefixWord ++ tailWord_795231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795266 : List Nat := [3, 4, 3, 1, 1, 1, 1, 2, 3, 1, 3]
def baseStart_795266 : Nat := 118140960795 + 795266 * 2 ^ 59
def prefixEnd_795266 : Nat := 4983230072969 + 3 ^ 40 * 795266 * 2
def baseEnd_795266 : Nat := 408353706178590751817645

theorem tailTrace_795266 : CollatzResearch.WordTrace tailWord_795266 prefixEnd_795266 408353706178590751817645 := by
  unfold tailWord_795266
  simp only [CollatzResearch.WordTrace]
  refine ⟨7251433484223644366169413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19337155957929718309785101 7251433484223644366169413)
  ·
    refine ⟨1359643778291933318656765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7251433484223644366169413 1359643778291933318656765)
    ·
      refine ⟨509866416859474994496287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1359643778291933318656765 509866416859474994496287)
      ·
        refine ⟨764799625289212491744431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 509866416859474994496287 764799625289212491744431)
        ·
          refine ⟨1147199437933818737616647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 764799625289212491744431 1147199437933818737616647)
          ·
            refine ⟨1720799156900728106424971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1147199437933818737616647 1720799156900728106424971)
            ·
              refine ⟨2581198735351092159637457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1720799156900728106424971 2581198735351092159637457)
              ·
                refine ⟨1935899051513319119728093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2581198735351092159637457 1935899051513319119728093)
                ·
                  refine ⟨725962144317494669898035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1935899051513319119728093 725962144317494669898035)
                  ·
                    refine ⟨1088943216476242004847053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 725962144317494669898035 1088943216476242004847053)
                    ·
                      refine ⟨408353706178590751817645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1088943216476242004847053 408353706178590751817645)
                      ·
                        rfl

theorem cell23_795266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_795266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_795266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_795266 prefixEnd_795266 := by exact prefixLift 795266
  have htrace : WordTrace (prefixWord ++ tailWord_795266) baseStart_795266 baseEnd_795266 := by
    simpa [prefixWord, tailWord_795266, baseEnd_795266] using wordTrace_append hprefix tailTrace_795266
  have hstable : (prefixWord ++ tailWord_795266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795266).length < 2 ^ (prefixWord ++ tailWord_795266).sum := by decide
  have hdescent : baseEnd_795266 < baseStart_795266 := by decide
  rcases family_descends (prefixWord ++ tailWord_795266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795268 : List Nat := [2, 3, 2, 1, 3, 1, 1, 3, 1, 2, 4]
def baseStart_795268 : Nat := 118140960795 + 795268 * 2 ^ 59
def prefixEnd_795268 : Nat := 4983230072969 + 3 ^ 40 * 795268 * 2
def baseEnd_795268 : Nat := 408354733139899743992635

theorem tailTrace_795268 : CollatzResearch.WordTrace tailWord_795268 prefixEnd_795268 408354733139899743992635 := by
  unfold tailWord_795268
  simp only [CollatzResearch.WordTrace]
  refine ⟨14502903441443665903125229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19337204588591554537500305 14502903441443665903125229)
  ·
    refine ⟨5438588790541374713671961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14502903441443665903125229 5438588790541374713671961)
    ·
      refine ⟨4078941592906031035253971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5438588790541374713671961 4078941592906031035253971)
      ·
        refine ⟨6118412389359046552880957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4078941592906031035253971 6118412389359046552880957)
        ·
          refine ⟨2294404646009642457330359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6118412389359046552880957 2294404646009642457330359)
          ·
            refine ⟨3441606969014463685995539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2294404646009642457330359 3441606969014463685995539)
            ·
              refine ⟨5162410453521695528993309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3441606969014463685995539 5162410453521695528993309)
              ·
                refine ⟨1935903920070635823372491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5162410453521695528993309 1935903920070635823372491)
                ·
                  refine ⟨2903855880105953735058737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1935903920070635823372491 2903855880105953735058737)
                  ·
                    refine ⟨2177891910079465301294053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2903855880105953735058737 2177891910079465301294053)
                    ·
                      refine ⟨408354733139899743992635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2177891910079465301294053 408354733139899743992635)
                      ·
                        rfl

theorem cell23_795268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_795268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_795268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_795268 prefixEnd_795268 := by exact prefixLift 795268
  have htrace : WordTrace (prefixWord ++ tailWord_795268) baseStart_795268 baseEnd_795268 := by
    simpa [prefixWord, tailWord_795268, baseEnd_795268] using wordTrace_append hprefix tailTrace_795268
  have hstable : (prefixWord ++ tailWord_795268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795268).length < 2 ^ (prefixWord ++ tailWord_795268).sum := by decide
  have hdescent : baseEnd_795268 < baseStart_795268 := by decide
  rcases family_descends (prefixWord ++ tailWord_795268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795278 : List Nat := [4, 1, 1, 3, 1, 1, 5, 7]
def baseStart_795278 : Nat := 118140960795 + 795278 * 2 ^ 59
def prefixEnd_795278 : Nat := 4983230072969 + 3 ^ 40 * 795278 * 2
def baseEnd_795278 : Nat := 15124439553572026106207

theorem tailTrace_795278 : CollatzResearch.WordTrace tailWord_795278 prefixEnd_795278 15124439553572026106207 := by
  unfold tailWord_795278
  simp only [CollatzResearch.WordTrace]
  refine ⟨3625771451606387939264311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19337447741900735676076325 3625771451606387939264311)
  ·
    refine ⟨5438657177409581908896467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3625771451606387939264311 5438657177409581908896467)
    ·
      refine ⟨8157985766114372863344701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5438657177409581908896467 8157985766114372863344701)
      ·
        refine ⟨3059244662292889823754263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8157985766114372863344701 3059244662292889823754263)
        ·
          refine ⟨4588866993439334735631395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3059244662292889823754263 4588866993439334735631395)
          ·
            refine ⟨6883300490159002103447093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4588866993439334735631395 6883300490159002103447093)
            ·
              refine ⟨645309420952406447198165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6883300490159002103447093 645309420952406447198165)
              ·
                refine ⟨15124439553572026106207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 645309420952406447198165 15124439553572026106207)
                ·
                  rfl

theorem cell23_795278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 5, 7].length) (baseStart_795278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_795278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_795278 prefixEnd_795278 := by exact prefixLift 795278
  have htrace : WordTrace (prefixWord ++ tailWord_795278) baseStart_795278 baseEnd_795278 := by
    simpa [prefixWord, tailWord_795278, baseEnd_795278] using wordTrace_append hprefix tailTrace_795278
  have hstable : (prefixWord ++ tailWord_795278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795278).length < 2 ^ (prefixWord ++ tailWord_795278).sum := by decide
  have hdescent : baseEnd_795278 < baseStart_795278 := by decide
  rcases family_descends (prefixWord ++ tailWord_795278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795288 : List Nat := [2, 1, 2, 4, 1, 1, 1, 4, 1, 3, 3]
def baseStart_795288 : Nat := 118140960795 + 795288 * 2 ^ 59
def prefixEnd_795288 : Nat := 4983230072969 + 3 ^ 40 * 795288 * 2
def baseEnd_795288 : Nat := 408365002752989665742543

theorem tailTrace_795288 : CollatzResearch.WordTrace tailWord_795288 prefixEnd_795288 408365002752989665742543 := by
  unfold tailWord_795288
  simp only [CollatzResearch.WordTrace]
  refine ⟨14503268171407437610989259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19337690895209916814652345 14503268171407437610989259)
  ·
    refine ⟨21754902257111156416483889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14503268171407437610989259 21754902257111156416483889)
    ·
      refine ⟨16316176692833367312362917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21754902257111156416483889 16316176692833367312362917)
      ·
        refine ⟨3059283129906256371068047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16316176692833367312362917 3059283129906256371068047)
        ·
          refine ⟨4588924694859384556602071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3059283129906256371068047 4588924694859384556602071)
          ·
            refine ⟨6883387042289076834903107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4588924694859384556602071 6883387042289076834903107)
            ·
              refine ⟨10325080563433615252354661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6883387042289076834903107 10325080563433615252354661)
              ·
                refine ⟨1935952605643802859816499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10325080563433615252354661 1935952605643802859816499)
                ·
                  refine ⟨2903928908465704289724749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1935952605643802859816499 2903928908465704289724749)
                  ·
                    refine ⟨1088973340674639108646781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2903928908465704289724749 1088973340674639108646781)
                    ·
                      refine ⟨408365002752989665742543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1088973340674639108646781 408365002752989665742543)
                      ·
                        rfl

theorem cell23_795288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_795288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_795288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_795288 prefixEnd_795288 := by exact prefixLift 795288
  have htrace : WordTrace (prefixWord ++ tailWord_795288) baseStart_795288 baseEnd_795288 := by
    simpa [prefixWord, tailWord_795288, baseEnd_795288] using wordTrace_append hprefix tailTrace_795288
  have hstable : (prefixWord ++ tailWord_795288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795288).length < 2 ^ (prefixWord ++ tailWord_795288).sum := by decide
  have hdescent : baseEnd_795288 < baseStart_795288 := by decide
  rcases family_descends (prefixWord ++ tailWord_795288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795292 : List Nat := [2, 2, 3, 2, 2, 1, 4, 1, 1, 2, 3]
def baseStart_795292 : Nat := 118140960795 + 795292 * 2 ^ 59
def prefixEnd_795292 : Nat := 4983230072969 + 3 ^ 40 * 795292 * 2
def baseEnd_795292 : Nat := 408367056675607650092525

theorem tailTrace_795292 : CollatzResearch.WordTrace tailWord_795292 prefixEnd_795292 408367056675607650092525 := by
  unfold tailWord_795292
  simp only [CollatzResearch.WordTrace]
  refine ⟨14503341117400191952562065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19337788156533589270082753 14503341117400191952562065)
  ·
    refine ⟨10877505838050143964421549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14503341117400191952562065 10877505838050143964421549)
    ·
      refine ⟨4079064689268803986658081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10877505838050143964421549 4079064689268803986658081)
      ·
        refine ⟨3059298516951602989993561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4079064689268803986658081 3059298516951602989993561)
        ·
          refine ⟨2294473887713702242495171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3059298516951602989993561 2294473887713702242495171)
          ·
            refine ⟨3441710831570553363742757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2294473887713702242495171 3441710831570553363742757)
            ·
              refine ⟨645320780919478755701767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3441710831570553363742757 645320780919478755701767)
              ·
                refine ⟨967981171379218133552651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 645320780919478755701767 967981171379218133552651)
                ·
                  refine ⟨1451971757068827200328977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 967981171379218133552651 1451971757068827200328977)
                  ·
                    refine ⟨1088978817801620400246733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1451971757068827200328977 1088978817801620400246733)
                    ·
                      refine ⟨408367056675607650092525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1088978817801620400246733 408367056675607650092525)
                      ·
                        rfl

theorem cell23_795292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_795292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_795292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_795292 prefixEnd_795292 := by exact prefixLift 795292
  have htrace : WordTrace (prefixWord ++ tailWord_795292) baseStart_795292 baseEnd_795292 := by
    simpa [prefixWord, tailWord_795292, baseEnd_795292] using wordTrace_append hprefix tailTrace_795292
  have hstable : (prefixWord ++ tailWord_795292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795292).length < 2 ^ (prefixWord ++ tailWord_795292).sum := by decide
  have hdescent : baseEnd_795292 < baseStart_795292 := by decide
  rcases family_descends (prefixWord ++ tailWord_795292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795306 : List Nat := [3, 1, 5, 2, 1, 1, 2, 1, 3, 2, 2]
def baseStart_795306 : Nat := 118140960795 + 795306 * 2 ^ 59
def prefixEnd_795306 : Nat := 4983230072969 + 3 ^ 40 * 795306 * 2
def baseEnd_795306 : Nat := 408374245404770595317461

theorem tailTrace_795306 : CollatzResearch.WordTrace tailWord_795306 prefixEnd_795306 408374245404770595317461 := by
  unfold tailWord_795306
  simp only [CollatzResearch.WordTrace]
  refine ⟨7251798214187416074033443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19338128571166442864089181 7251798214187416074033443)
  ·
    refine ⟨10877697321281124111050165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7251798214187416074033443 10877697321281124111050165)
    ·
      refine ⟨1019784123870105385410953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10877697321281124111050165 1019784123870105385410953)
      ·
        refine ⟨764838092902579039058215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1019784123870105385410953 764838092902579039058215)
        ·
          refine ⟨1147257139353868558587323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 764838092902579039058215 1147257139353868558587323)
          ·
            refine ⟨1720885709030802837880985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1147257139353868558587323 1720885709030802837880985)
            ·
              refine ⟨1290664281773102128410739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1720885709030802837880985 1290664281773102128410739)
              ·
                refine ⟨1935996422659653192616109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1290664281773102128410739 1935996422659653192616109)
                ·
                  refine ⟨725998658497369947231041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1935996422659653192616109 725998658497369947231041)
                  ·
                    refine ⟨544498993873027460423281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 725998658497369947231041 544498993873027460423281)
                    ·
                      refine ⟨408374245404770595317461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 544498993873027460423281 408374245404770595317461)
                      ·
                        rfl

theorem cell23_795306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_795306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_795306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_795306 prefixEnd_795306 := by exact prefixLift 795306
  have htrace : WordTrace (prefixWord ++ tailWord_795306) baseStart_795306 baseEnd_795306 := by
    simpa [prefixWord, tailWord_795306, baseEnd_795306] using wordTrace_append hprefix tailTrace_795306
  have hstable : (prefixWord ++ tailWord_795306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795306).length < 2 ^ (prefixWord ++ tailWord_795306).sum := by decide
  have hdescent : baseEnd_795306 < baseStart_795306 := by decide
  rcases family_descends (prefixWord ++ tailWord_795306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795322 : List Nat := [3, 1, 1, 1, 2, 3, 5, 1, 2, 1, 3]
def baseStart_795322 : Nat := 118140960795 + 795322 * 2 ^ 59
def prefixEnd_795322 : Nat := 4983230072969 + 3 ^ 40 * 795322 * 2
def baseEnd_795322 : Nat := 408382461095242532717387

theorem tailTrace_795322 : CollatzResearch.WordTrace tailWord_795322 prefixEnd_795322 408382461095242532717387 := by
  unfold tailWord_795322
  simp only [CollatzResearch.WordTrace]
  refine ⟨7251944106172924757179055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19338517616461132685810813 7251944106172924757179055)
  ·
    refine ⟨10877916159259387135768583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7251944106172924757179055 10877916159259387135768583)
    ·
      refine ⟨16316874238889080703652875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10877916159259387135768583 16316874238889080703652875)
      ·
        refine ⟨24475311358333621055479313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16316874238889080703652875 24475311358333621055479313)
        ·
          refine ⟨18356483518750215791609485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24475311358333621055479313 18356483518750215791609485)
          ·
            refine ⟨6883681319531330921853557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18356483518750215791609485 6883681319531330921853557)
            ·
              refine ⟨645345123706062273923771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6883681319531330921853557 645345123706062273923771)
              ·
                refine ⟨968017685559093410885657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 645345123706062273923771 968017685559093410885657)
                ·
                  refine ⟨726013264169320058164243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 968017685559093410885657 726013264169320058164243)
                  ·
                    refine ⟨1089019896253980087246365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 726013264169320058164243 1089019896253980087246365)
                    ·
                      refine ⟨408382461095242532717387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1089019896253980087246365 408382461095242532717387)
                      ·
                        rfl

theorem cell23_795322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5, 1, 2, 1, 3].length) (baseStart_795322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_795322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_795322 prefixEnd_795322 := by exact prefixLift 795322
  have htrace : WordTrace (prefixWord ++ tailWord_795322) baseStart_795322 baseEnd_795322 := by
    simpa [prefixWord, tailWord_795322, baseEnd_795322] using wordTrace_append hprefix tailTrace_795322
  have hstable : (prefixWord ++ tailWord_795322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795322).length < 2 ^ (prefixWord ++ tailWord_795322).sum := by decide
  have hdescent : baseEnd_795322 < baseStart_795322 := by decide
  rcases family_descends (prefixWord ++ tailWord_795322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795329 : List Nat := [1, 2, 6, 2, 2, 1, 2, 7]
def baseStart_795329 : Nat := 118140960795 + 795329 * 2 ^ 59
def prefixEnd_795329 : Nat := 4983230072969 + 3 ^ 40 * 795329 * 2
def baseEnd_795329 : Nat := 15125409461474963160365

theorem tailTrace_795329 : CollatzResearch.WordTrace tailWord_795329 prefixEnd_795329 15125409461474963160365 := by
  unfold tailWord_795329
  simp only [CollatzResearch.WordTrace]
  refine ⟨29008031735666339224221041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19338687823777559482814027 29008031735666339224221041)
  ·
    refine ⟨21756023801749754418165781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29008031735666339224221041 21756023801749754418165781)
    ·
      refine ⟨1019813615707019738351521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 21756023801749754418165781 1019813615707019738351521)
      ·
        refine ⟨764860211780264803763641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1019813615707019738351521 764860211780264803763641)
        ·
          refine ⟨573645158835198602822731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 764860211780264803763641 573645158835198602822731)
          ·
            refine ⟨860467738252797904234097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 573645158835198602822731 860467738252797904234097)
            ·
              refine ⟨645350803689598428175573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 860467738252797904234097 645350803689598428175573)
              ·
                refine ⟨15125409461474963160365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 645350803689598428175573 15125409461474963160365)
                ·
                  rfl

theorem cell23_795329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 2, 7].length) (baseStart_795329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_795329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_795329 prefixEnd_795329 := by exact prefixLift 795329
  have htrace : WordTrace (prefixWord ++ tailWord_795329) baseStart_795329 baseEnd_795329 := by
    simpa [prefixWord, tailWord_795329, baseEnd_795329] using wordTrace_append hprefix tailTrace_795329
  have hstable : (prefixWord ++ tailWord_795329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795329).length < 2 ^ (prefixWord ++ tailWord_795329).sum := by decide
  have hdescent : baseEnd_795329 < baseStart_795329 := by decide
  rcases family_descends (prefixWord ++ tailWord_795329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795332 : List Nat := [2, 3, 3, 1, 1, 2, 1, 4, 1, 3, 2]
def baseStart_795332 : Nat := 118140960795 + 795332 * 2 ^ 59
def prefixEnd_795332 : Nat := 4983230072969 + 3 ^ 40 * 795332 * 2
def baseEnd_795332 : Nat := 408387595901787493592341

theorem tailTrace_795332 : CollatzResearch.WordTrace tailWord_795332 prefixEnd_795332 408387595901787493592341 := by
  unfold tailWord_795332
  simp only [CollatzResearch.WordTrace]
  refine ⟨14504070577327735368290125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19338760769770313824386833 14504070577327735368290125)
  ·
    refine ⟨5439026466497900763108797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14504070577327735368290125 5439026466497900763108797)
    ·
      refine ⟨2039634924936712786165799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5439026466497900763108797 2039634924936712786165799)
      ·
        refine ⟨3059452387405069179248699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2039634924936712786165799 3059452387405069179248699)
        ·
          refine ⟨4589178581107603768873049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3059452387405069179248699 4589178581107603768873049)
          ·
            refine ⟨3441883935830702826654787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4589178581107603768873049 3441883935830702826654787)
            ·
              refine ⟨5162825903746054239982181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3441883935830702826654787 5162825903746054239982181)
              ·
                refine ⟨968029856952385169996659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5162825903746054239982181 968029856952385169996659)
                ·
                  refine ⟨1452044785428577754994989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 968029856952385169996659 1452044785428577754994989)
                  ·
                    refine ⟨544516794535716658123121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1452044785428577754994989 544516794535716658123121)
                    ·
                      refine ⟨408387595901787493592341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 544516794535716658123121 408387595901787493592341)
                      ·
                        rfl

theorem cell23_795332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_795332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_795332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_795332 prefixEnd_795332 := by exact prefixLift 795332
  have htrace : WordTrace (prefixWord ++ tailWord_795332) baseStart_795332 baseEnd_795332 := by
    simpa [prefixWord, tailWord_795332, baseEnd_795332] using wordTrace_append hprefix tailTrace_795332
  have hstable : (prefixWord ++ tailWord_795332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795332).length < 2 ^ (prefixWord ++ tailWord_795332).sum := by decide
  have hdescent : baseEnd_795332 < baseStart_795332 := by decide
  rcases family_descends (prefixWord ++ tailWord_795332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795345 : List Nat := [1, 2, 2, 1, 2, 3, 1, 1, 6, 2, 2]
def baseStart_795345 : Nat := 118140960795 + 795345 * 2 ^ 59
def prefixEnd_795345 : Nat := 4983230072969 + 3 ^ 40 * 795345 * 2
def baseEnd_795345 : Nat := 408394271150295942729781

theorem tailTrace_795345 : CollatzResearch.WordTrace tailWord_795345 prefixEnd_795345 408394271150295942729781 := by
  unfold tailWord_795345
  simp only [CollatzResearch.WordTrace]
  refine ⟨29008615303608373956803489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19339076869072249304535659 29008615303608373956803489)
  ·
    refine ⟨21756461477706280467602617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29008615303608373956803489 21756461477706280467602617)
    ·
      refine ⟨16317346108279710350701963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21756461477706280467602617 16317346108279710350701963)
      ·
        refine ⟨24476019162419565526052945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16317346108279710350701963 24476019162419565526052945)
        ·
          refine ⟨18357014371814674144539709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24476019162419565526052945 18357014371814674144539709)
          ·
            refine ⟨6883880389430502804202391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18357014371814674144539709 6883880389430502804202391)
            ·
              refine ⟨10325820584145754206303587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6883880389430502804202391 10325820584145754206303587)
              ·
                refine ⟨15488730876218631309455381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10325820584145754206303587 15488730876218631309455381)
                ·
                  refine ⟨726034259822748342630721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 15488730876218631309455381 726034259822748342630721)
                  ·
                    refine ⟨544525694867061256973041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 726034259822748342630721 544525694867061256973041)
                    ·
                      refine ⟨408394271150295942729781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 544525694867061256973041 408394271150295942729781)
                      ·
                        rfl

theorem cell23_795345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 6, 2, 2].length) (baseStart_795345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_795345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_795345 prefixEnd_795345 := by exact prefixLift 795345
  have htrace : WordTrace (prefixWord ++ tailWord_795345) baseStart_795345 baseEnd_795345 := by
    simpa [prefixWord, tailWord_795345, baseEnd_795345] using wordTrace_append hprefix tailTrace_795345
  have hstable : (prefixWord ++ tailWord_795345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795345).length < 2 ^ (prefixWord ++ tailWord_795345).sum := by decide
  have hdescent : baseEnd_795345 < baseStart_795345 := by decide
  rcases family_descends (prefixWord ++ tailWord_795345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795391 : List Nat := [1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 7]
def baseStart_795391 : Nat := 118140960795 + 795391 * 2 ^ 59
def prefixEnd_795391 : Nat := 4983230072969 + 3 ^ 40 * 795391 * 2
def baseEnd_795391 : Nat := 408417891260402762754569

theorem tailTrace_795391 : CollatzResearch.WordTrace tailWord_795391 prefixEnd_795391 408417891260402762754569 := by
  unfold tailWord_795391
  simp only [CollatzResearch.WordTrace]
  refine ⟨29010293061441723812978027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19340195374294482541985351 29010293061441723812978027)
  ·
    refine ⟨43515439592162585719467041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29010293061441723812978027 43515439592162585719467041)
    ·
      refine ⟨32636579694121939289600281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43515439592162585719467041 32636579694121939289600281)
      ·
        refine ⟨24477434770591454467200211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32636579694121939289600281 24477434770591454467200211)
        ·
          refine ⟨36716152155887181700800317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24477434770591454467200211 36716152155887181700800317)
          ·
            refine ⟨13768557058457693137800119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36716152155887181700800317 13768557058457693137800119)
            ·
              refine ⟨20652835587686539706700179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13768557058457693137800119 20652835587686539706700179)
              ·
                refine ⟨30979253381529809560050269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20652835587686539706700179 30979253381529809560050269)
                ·
                  refine ⟨11617220018073678585018851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30979253381529809560050269 11617220018073678585018851)
                  ·
                    refine ⟨17425830027110517877528277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11617220018073678585018851 17425830027110517877528277)
                    ·
                      refine ⟨408417891260402762754569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 17425830027110517877528277 408417891260402762754569)
                      ·
                        rfl

theorem cell23_795391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 7].length) (baseStart_795391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_795391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_795391 prefixEnd_795391 := by exact prefixLift 795391
  have htrace : WordTrace (prefixWord ++ tailWord_795391) baseStart_795391 baseEnd_795391 := by
    simpa [prefixWord, tailWord_795391, baseEnd_795391] using wordTrace_append hprefix tailTrace_795391
  have hstable : (prefixWord ++ tailWord_795391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795391).length < 2 ^ (prefixWord ++ tailWord_795391).sum := by decide
  have hdescent : baseEnd_795391 < baseStart_795391 := by decide
  rcases family_descends (prefixWord ++ tailWord_795391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795445 : List Nat := [1, 3, 3, 1, 3, 1, 1, 1, 5, 4]
def baseStart_795445 : Nat := 118140960795 + 795445 * 2 ^ 59
def prefixEnd_795445 : Nat := 4983230072969 + 3 ^ 40 * 795445 * 2
def baseEnd_795445 : Nat := 136148539738581850493107

theorem tailTrace_795445 : CollatzResearch.WordTrace tailWord_795445 prefixEnd_795445 136148539738581850493107 := by
  unfold tailWord_795445
  simp only [CollatzResearch.WordTrace]
  refine ⟨29012262603246091035443789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19341508402164060690295859 29012262603246091035443789)
  ·
    refine ⟨10879598476217284138291421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29012262603246091035443789 10879598476217284138291421)
    ·
      refine ⟨4079849428581481551859283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10879598476217284138291421 4079849428581481551859283)
      ·
        refine ⟨6119774142872222327788925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4079849428581481551859283 6119774142872222327788925)
        ·
          refine ⟨2294915303577083372920847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6119774142872222327788925 2294915303577083372920847)
          ·
            refine ⟨3442372955365625059381271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2294915303577083372920847 3442372955365625059381271)
            ·
              refine ⟨5163559433048437589071907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3442372955365625059381271 5163559433048437589071907)
              ·
                refine ⟨7745339149572656383607861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5163559433048437589071907 7745339149572656383607861)
                ·
                  refine ⟨726125545272436535963237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7745339149572656383607861 726125545272436535963237)
                  ·
                    refine ⟨136148539738581850493107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 726125545272436535963237 136148539738581850493107)
                    ·
                      rfl

theorem cell23_795445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_795445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_795445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_795445 prefixEnd_795445 := by exact prefixLift 795445
  have htrace : WordTrace (prefixWord ++ tailWord_795445) baseStart_795445 baseEnd_795445 := by
    simpa [prefixWord, tailWord_795445, baseEnd_795445] using wordTrace_append hprefix tailTrace_795445
  have hstable : (prefixWord ++ tailWord_795445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795445).length < 2 ^ (prefixWord ++ tailWord_795445).sum := by decide
  have hdescent : baseEnd_795445 < baseStart_795445 := by decide
  rcases family_descends (prefixWord ++ tailWord_795445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795455 : List Nat := [1, 1, 2, 2, 5, 2, 1, 1, 1, 4, 3]
def baseStart_795455 : Nat := 118140960795 + 795455 * 2 ^ 59
def prefixEnd_795455 : Nat := 4983230072969 + 3 ^ 40 * 795455 * 2
def baseEnd_795455 : Nat := 408450754022290512354275

theorem tailTrace_795455 : CollatzResearch.WordTrace tailWord_795455 prefixEnd_795455 408450754022290512354275 := by
  unfold tailWord_795455
  simp only [CollatzResearch.WordTrace]
  refine ⟨29012627333209862743307819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19341751555473241828871879 29012627333209862743307819)
  ·
    refine ⟨43518940999814794114961729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29012627333209862743307819 43518940999814794114961729)
    ·
      refine ⟨32639205749861095586221297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43518940999814794114961729 32639205749861095586221297)
      ·
        refine ⟨24479404312395821689665973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32639205749861095586221297 24479404312395821689665973)
        ·
          refine ⟨2294944154287108283406185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24479404312395821689665973 2294944154287108283406185)
          ·
            refine ⟨1721208115715331212554639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2294944154287108283406185 1721208115715331212554639)
            ·
              refine ⟨2581812173572996818831959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1721208115715331212554639 2581812173572996818831959)
              ·
                refine ⟨3872718260359495228247939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2581812173572996818831959 3872718260359495228247939)
                ·
                  refine ⟨5809077390539242842371909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3872718260359495228247939 5809077390539242842371909)
                  ·
                    refine ⟨1089202010726108032944733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5809077390539242842371909 1089202010726108032944733)
                    ·
                      refine ⟨408450754022290512354275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1089202010726108032944733 408450754022290512354275)
                      ·
                        rfl

theorem cell23_795455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 4, 3].length) (baseStart_795455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_795455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_795455 prefixEnd_795455 := by exact prefixLift 795455
  have htrace : WordTrace (prefixWord ++ tailWord_795455) baseStart_795455 baseEnd_795455 := by
    simpa [prefixWord, tailWord_795455, baseEnd_795455] using wordTrace_append hprefix tailTrace_795455
  have hstable : (prefixWord ++ tailWord_795455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795455).length < 2 ^ (prefixWord ++ tailWord_795455).sum := by decide
  have hdescent : baseEnd_795455 < baseStart_795455 := by decide
  rcases family_descends (prefixWord ++ tailWord_795455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795492 : List Nat := [2, 3, 1, 1, 4, 2, 3, 1, 6]
def baseStart_795492 : Nat := 118140960795 + 795492 * 2 ^ 59
def prefixEnd_795492 : Nat := 4983230072969 + 3 ^ 40 * 795492 * 2
def baseEnd_795492 : Nat := 45385528089611874176845

theorem tailTrace_795492 : CollatzResearch.WordTrace tailWord_795492 prefixEnd_795492 45385528089611874176845 := by
  unfold tailWord_795492
  simp only [CollatzResearch.WordTrace]
  refine ⟨14506988417037909031202365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19342651222717212041603153 14506988417037909031202365)
  ·
    refine ⟨5440120656389215886700887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14506988417037909031202365 5440120656389215886700887)
    ·
      refine ⟨8160180984583823830051331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5440120656389215886700887 8160180984583823830051331)
      ·
        refine ⟨12240271476875735745076997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8160180984583823830051331 12240271476875735745076997)
        ·
          refine ⟨2295050901914200452201937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12240271476875735745076997 2295050901914200452201937)
          ·
            refine ⟨1721288176435650339151453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2295050901914200452201937 1721288176435650339151453)
            ·
              refine ⟨645483066163368877181795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1721288176435650339151453 645483066163368877181795)
              ·
                refine ⟨968224599245053315772693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 645483066163368877181795 968224599245053315772693)
                ·
                  refine ⟨45385528089611874176845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 968224599245053315772693 45385528089611874176845)
                  ·
                    rfl

theorem cell23_795492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 3, 1, 6].length) (baseStart_795492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_795492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_795492 prefixEnd_795492 := by exact prefixLift 795492
  have htrace : WordTrace (prefixWord ++ tailWord_795492) baseStart_795492 baseEnd_795492 := by
    simpa [prefixWord, tailWord_795492, baseEnd_795492] using wordTrace_append hprefix tailTrace_795492
  have hstable : (prefixWord ++ tailWord_795492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795492).length < 2 ^ (prefixWord ++ tailWord_795492).sum := by decide
  have hdescent : baseEnd_795492 < baseStart_795492 := by decide
  rcases family_descends (prefixWord ++ tailWord_795492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795505 : List Nat := [1, 2, 2, 2, 1, 4, 1, 4, 1, 5]
def baseStart_795505 : Nat := 118140960795 + 795505 * 2 ^ 59
def prefixEnd_795505 : Nat := 4983230072969 + 3 ^ 40 * 795505 * 2
def baseEnd_795505 : Nat := 136158809351671772243015

theorem tailTrace_795505 : CollatzResearch.WordTrace tailWord_795505 prefixEnd_795505 136158809351671772243015 := by
  unfold tailWord_795505
  simp only [CollatzResearch.WordTrace]
  refine ⟨29014450983028721282627969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19342967322019147521751979 29014450983028721282627969)
  ·
    refine ⟨21760838237271540961970977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29014450983028721282627969 21760838237271540961970977)
    ·
      refine ⟨16320628677953655721478233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21760838237271540961970977 16320628677953655721478233)
      ·
        refine ⟨12240471508465241791108675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16320628677953655721478233 12240471508465241791108675)
        ·
          refine ⟨18360707262697862686663013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12240471508465241791108675 18360707262697862686663013)
          ·
            refine ⟨3442632611755849253749315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18360707262697862686663013 3442632611755849253749315)
            ·
              refine ⟨5163948917633773880623973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3442632611755849253749315 5163948917633773880623973)
              ·
                refine ⟨968240422056332602616995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5163948917633773880623973 968240422056332602616995)
                ·
                  refine ⟨1452360633084498903925493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 968240422056332602616995 1452360633084498903925493)
                  ·
                    refine ⟨136158809351671772243015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1452360633084498903925493 136158809351671772243015)
                    ·
                      rfl

theorem cell23_795505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 4, 1, 5].length) (baseStart_795505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_795505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_795505 prefixEnd_795505 := by exact prefixLift 795505
  have htrace : WordTrace (prefixWord ++ tailWord_795505) baseStart_795505 baseEnd_795505 := by
    simpa [prefixWord, tailWord_795505, baseEnd_795505] using wordTrace_append hprefix tailTrace_795505
  have hstable : (prefixWord ++ tailWord_795505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795505).length < 2 ^ (prefixWord ++ tailWord_795505).sum := by decide
  have hdescent : baseEnd_795505 < baseStart_795505 := by decide
  rcases family_descends (prefixWord ++ tailWord_795505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795519 : List Nat := [1, 1, 2, 2, 1, 1, 7, 3, 1, 1, 3]
def baseStart_795519 : Nat := 118140960795 + 795519 * 2 ^ 59
def prefixEnd_795519 : Nat := 4983230072969 + 3 ^ 40 * 795519 * 2
def baseEnd_795519 : Nat := 408483616784178261953981

theorem tailTrace_795519 : CollatzResearch.WordTrace tailWord_795519 prefixEnd_795519 408483616784178261953981 := by
  unfold tailWord_795519
  simp only [CollatzResearch.WordTrace]
  refine ⟨29014961604978001673637611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19343307736652001115758407 29014961604978001673637611)
  ·
    refine ⟨43522442407467002510456417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29014961604978001673637611 43522442407467002510456417)
    ·
      refine ⟨32641831805600251882842313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43522442407467002510456417 32641831805600251882842313)
      ·
        refine ⟨24481373854200188912131735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32641831805600251882842313 24481373854200188912131735)
        ·
          refine ⟨36722060781300283368197603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24481373854200188912131735 36722060781300283368197603)
          ·
            refine ⟨55083091171950425052296405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36722060781300283368197603 55083091171950425052296405)
            ·
              refine ⟨1291009949342588087163197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 55083091171950425052296405 1291009949342588087163197)
              ·
                refine ⟨484128731003470532686199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1291009949342588087163197 484128731003470532686199)
                ·
                  refine ⟨726193096505205799029299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 484128731003470532686199 726193096505205799029299)
                  ·
                    refine ⟨1089289644757808698543949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 726193096505205799029299 1089289644757808698543949)
                    ·
                      refine ⟨408483616784178261953981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1089289644757808698543949 408483616784178261953981)
                      ·
                        rfl

theorem cell23_795519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 3, 1, 1, 3].length) (baseStart_795519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_795519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_795519 prefixEnd_795519 := by exact prefixLift 795519
  have htrace : WordTrace (prefixWord ++ tailWord_795519) baseStart_795519 baseEnd_795519 := by
    simpa [prefixWord, tailWord_795519, baseEnd_795519] using wordTrace_append hprefix tailTrace_795519
  have hstable : (prefixWord ++ tailWord_795519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795519).length < 2 ^ (prefixWord ++ tailWord_795519).sum := by decide
  have hdescent : baseEnd_795519 < baseStart_795519 := by decide
  rcases family_descends (prefixWord ++ tailWord_795519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795545 : List Nat := [1, 2, 1, 2, 1, 3, 1, 4, 3, 2, 3]
def baseStart_795545 : Nat := 118140960795 + 795545 * 2 ^ 59
def prefixEnd_795545 : Nat := 4983230072969 + 3 ^ 40 * 795545 * 2
def baseEnd_795545 : Nat := 408496967281195160228861

theorem tailTrace_795545 : CollatzResearch.WordTrace tailWord_795545 prefixEnd_795545 408496967281195160228861 := by
  unfold tailWord_795545
  simp only [CollatzResearch.WordTrace]
  refine ⟨29015909902883808114084089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19343939935255872076056059 29015909902883808114084089)
  ·
    refine ⟨21761932427162856085563067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29015909902883808114084089 21761932427162856085563067)
    ·
      refine ⟨32642898640744284128344601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21761932427162856085563067 32642898640744284128344601)
      ·
        refine ⟨24482173980558213096258451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32642898640744284128344601 24482173980558213096258451)
        ·
          refine ⟨36723260970837319644387677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24482173980558213096258451 36723260970837319644387677)
          ·
            refine ⟨13771222864063994866645379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36723260970837319644387677 13771222864063994866645379)
            ·
              refine ⟨20656834296095992299968069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13771222864063994866645379 20656834296095992299968069)
              ·
                refine ⟨3873156430517998556244013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20656834296095992299968069 3873156430517998556244013)
                ·
                  refine ⟨1452433661444249458591505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3873156430517998556244013 1452433661444249458591505)
                  ·
                    refine ⟨1089325246083187093943629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1452433661444249458591505 1089325246083187093943629)
                    ·
                      refine ⟨408496967281195160228861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1089325246083187093943629 408496967281195160228861)
                      ·
                        rfl

theorem cell23_795545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 3, 2, 3].length) (baseStart_795545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_795545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_795545 prefixEnd_795545 := by exact prefixLift 795545
  have htrace : WordTrace (prefixWord ++ tailWord_795545) baseStart_795545 baseEnd_795545 := by
    simpa [prefixWord, tailWord_795545, baseEnd_795545] using wordTrace_append hprefix tailTrace_795545
  have hstable : (prefixWord ++ tailWord_795545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795545).length < 2 ^ (prefixWord ++ tailWord_795545).sum := by decide
  have hdescent : baseEnd_795545 < baseStart_795545 := by decide
  rcases family_descends (prefixWord ++ tailWord_795545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795575 : List Nat := [1, 1, 3, 1, 3, 1, 3, 1, 3, 3, 3]
def baseStart_795575 : Nat := 118140960795 + 795575 * 2 ^ 59
def prefixEnd_795575 : Nat := 4983230072969 + 3 ^ 40 * 795575 * 2
def baseEnd_795575 : Nat := 408512371700830042853723

theorem tailTrace_795575 : CollatzResearch.WordTrace tailWord_795575 prefixEnd_795575 408512371700830042853723 := by
  unfold tailWord_795575
  simp only [CollatzResearch.WordTrace]
  refine ⟨29017004092775123237676179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19344669395183415491784119 29017004092775123237676179)
  ·
    refine ⟨43525506139162684856514269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29017004092775123237676179 43525506139162684856514269)
    ·
      refine ⟨16322064802186006821192851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43525506139162684856514269 16322064802186006821192851)
      ·
        refine ⟨24483097203279010231789277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16322064802186006821192851 24483097203279010231789277)
        ·
          refine ⟨9181161451229628836920979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24483097203279010231789277 9181161451229628836920979)
          ·
            refine ⟨13771742176844443255381469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9181161451229628836920979 13771742176844443255381469)
            ·
              refine ⟨5164403316316666220768051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13771742176844443255381469 5164403316316666220768051)
              ·
                refine ⟨7746604974474999331152077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5164403316316666220768051 7746604974474999331152077)
                ·
                  refine ⟨2904976865428124749182029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7746604974474999331152077 2904976865428124749182029)
                  ·
                    refine ⟨1089366324535546780943261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2904976865428124749182029 1089366324535546780943261)
                    ·
                      refine ⟨408512371700830042853723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1089366324535546780943261 408512371700830042853723)
                      ·
                        rfl

theorem cell23_795575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 3, 3, 3].length) (baseStart_795575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_795575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_795575 prefixEnd_795575 := by exact prefixLift 795575
  have htrace : WordTrace (prefixWord ++ tailWord_795575) baseStart_795575 baseEnd_795575 := by
    simpa [prefixWord, tailWord_795575, baseEnd_795575] using wordTrace_append hprefix tailTrace_795575
  have hstable : (prefixWord ++ tailWord_795575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795575).length < 2 ^ (prefixWord ++ tailWord_795575).sum := by decide
  have hdescent : baseEnd_795575 < baseStart_795575 := by decide
  rcases family_descends (prefixWord ++ tailWord_795575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795609 : List Nat := [1, 2, 1, 2, 5, 1, 2, 3, 2, 1, 3]
def baseStart_795609 : Nat := 118140960795 + 795609 * 2 ^ 59
def prefixEnd_795609 : Nat := 4983230072969 + 3 ^ 40 * 795609 * 2
def baseEnd_795609 : Nat := 408529830043082909828567

theorem tailTrace_795609 : CollatzResearch.WordTrace tailWord_795609 prefixEnd_795609 408529830043082909828567 := by
  unfold tailWord_795609
  simp only [CollatzResearch.WordTrace]
  refine ⟨29018244174651947044413881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19345496116434631362942587 29018244174651947044413881)
  ·
    refine ⟨21763683130988960283310411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29018244174651947044413881 21763683130988960283310411)
    ·
      refine ⟨32645524696483440424965617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21763683130988960283310411 32645524696483440424965617)
      ·
        refine ⟨24484143522362580318724213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32645524696483440424965617 24484143522362580318724213)
        ·
          refine ⟨2295388455221491904880395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24484143522362580318724213 2295388455221491904880395)
          ·
            refine ⟨3443082682832237857320593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2295388455221491904880395 3443082682832237857320593)
            ·
              refine ⟨2582312012124178392990445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3443082682832237857320593 2582312012124178392990445)
              ·
                refine ⟨968367004546566897371417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2582312012124178392990445 968367004546566897371417)
                ·
                  refine ⟨726275253409925173028563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 968367004546566897371417 726275253409925173028563)
                  ·
                    refine ⟨1089412880114887759542845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 726275253409925173028563 1089412880114887759542845)
                    ·
                      refine ⟨408529830043082909828567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1089412880114887759542845 408529830043082909828567)
                      ·
                        rfl

theorem cell23_795609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 3, 2, 1, 3].length) (baseStart_795609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_795609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_795609 prefixEnd_795609 := by exact prefixLift 795609
  have htrace : WordTrace (prefixWord ++ tailWord_795609) baseStart_795609 baseEnd_795609 := by
    simpa [prefixWord, tailWord_795609, baseEnd_795609] using wordTrace_append hprefix tailTrace_795609
  have hstable : (prefixWord ++ tailWord_795609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795609).length < 2 ^ (prefixWord ++ tailWord_795609).sum := by decide
  have hdescent : baseEnd_795609 < baseStart_795609 := by decide
  rcases family_descends (prefixWord ++ tailWord_795609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795619 : List Nat := [1, 1, 1, 6, 1, 1, 2, 4, 1, 3, 2]
def baseStart_795619 : Nat := 118140960795 + 795619 * 2 ^ 59
def prefixEnd_795619 : Nat := 4983230072969 + 3 ^ 40 * 795619 * 2
def baseEnd_795619 : Nat := 408534964849627870703521

theorem tailTrace_795619 : CollatzResearch.WordTrace tailWord_795619 prefixEnd_795619 408534964849627870703521 := by
  unfold tailWord_795619
  simp only [CollatzResearch.WordTrace]
  refine ⟨29018608904615718752277911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19345739269743812501518607 29018608904615718752277911)
  ·
    refine ⟨43527913356923578128416867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29018608904615718752277911 43527913356923578128416867)
    ·
      refine ⟨65291870035385367192625301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43527913356923578128416867 65291870035385367192625301)
      ·
        refine ⟨3060556407908689087154311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 65291870035385367192625301 3060556407908689087154311)
        ·
          refine ⟨4590834611863033630731467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3060556407908689087154311 4590834611863033630731467)
          ·
            refine ⟨6886251917794550446097201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4590834611863033630731467 6886251917794550446097201)
            ·
              refine ⟨5164688938345912834572901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6886251917794550446097201 5164688938345912834572901)
              ·
                refine ⟨968379175939858656482419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5164688938345912834572901 968379175939858656482419)
                ·
                  refine ⟨1452568763909787984723629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 968379175939858656482419 1452568763909787984723629)
                  ·
                    refine ⟨544713286466170494271361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1452568763909787984723629 544713286466170494271361)
                    ·
                      refine ⟨408534964849627870703521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 544713286466170494271361 408534964849627870703521)
                      ·
                        rfl

theorem cell23_795619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_795619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_795619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_795619 prefixEnd_795619 := by exact prefixLift 795619
  have htrace : WordTrace (prefixWord ++ tailWord_795619) baseStart_795619 baseEnd_795619 := by
    simpa [prefixWord, tailWord_795619, baseEnd_795619] using wordTrace_append hprefix tailTrace_795619
  have hstable : (prefixWord ++ tailWord_795619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795619).length < 2 ^ (prefixWord ++ tailWord_795619).sum := by decide
  have hdescent : baseEnd_795619 < baseStart_795619 := by decide
  rcases family_descends (prefixWord ++ tailWord_795619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795662 : List Nat := [4, 1, 1, 2, 2, 2, 2, 1, 2, 2, 4]
def baseStart_795662 : Nat := 118140960795 + 795662 * 2 ^ 59
def prefixEnd_795662 : Nat := 4983230072969 + 3 ^ 40 * 795662 * 2
def baseEnd_795662 : Nat := 408557044517771202465823

theorem tailTrace_795662 : CollatzResearch.WordTrace tailWord_795662 prefixEnd_795662 408557044517771202465823 := by
  unfold tailWord_795662
  simp only [CollatzResearch.WordTrace]
  refine ⟨3627522155432492137011655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19346784828973291397395493 3627522155432492137011655)
  ·
    refine ⟨5441283233148738205517483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3627522155432492137011655 5441283233148738205517483)
    ·
      refine ⟨8161924849723107308276225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5441283233148738205517483 8161924849723107308276225)
      ·
        refine ⟨6121443637292330481207169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8161924849723107308276225 6121443637292330481207169)
        ·
          refine ⟨4591082727969247860905377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6121443637292330481207169 4591082727969247860905377)
          ·
            refine ⟨3443312045976935895679033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4591082727969247860905377 3443312045976935895679033)
            ·
              refine ⟨2582484034482701921759275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3443312045976935895679033 2582484034482701921759275)
              ·
                refine ⟨3873726051724052882638913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2582484034482701921759275 3873726051724052882638913)
                ·
                  refine ⟨2905294538793039661979185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3873726051724052882638913 2905294538793039661979185)
                  ·
                    refine ⟨2178970904094779746484389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2905294538793039661979185 2178970904094779746484389)
                    ·
                      refine ⟨408557044517771202465823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2178970904094779746484389 408557044517771202465823)
                      ·
                        rfl

theorem cell23_795662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_795662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_795662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_795662 prefixEnd_795662 := by exact prefixLift 795662
  have htrace : WordTrace (prefixWord ++ tailWord_795662) baseStart_795662 baseEnd_795662 := by
    simpa [prefixWord, tailWord_795662, baseEnd_795662] using wordTrace_append hprefix tailTrace_795662
  have hstable : (prefixWord ++ tailWord_795662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795662).length < 2 ^ (prefixWord ++ tailWord_795662).sum := by decide
  have hdescent : baseEnd_795662 < baseStart_795662 := by decide
  rcases family_descends (prefixWord ++ tailWord_795662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795685 : List Nat := [1, 3, 1, 2, 2, 2, 1, 3, 1, 7]
def baseStart_795685 : Nat := 118140960795 + 795685 * 2 ^ 59
def prefixEnd_795685 : Nat := 4983230072969 + 3 ^ 40 * 795685 * 2
def baseEnd_795685 : Nat := 136189618190941537492739

theorem tailTrace_795685 : CollatzResearch.WordTrace tailWord_795685 prefixEnd_795685 136189618190941537492739 := by
  unfold tailWord_795685
  simp only [CollatzResearch.WordTrace]
  refine ⟨29021016122376612024180509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19347344081584408016120339 29021016122376612024180509)
  ·
    refine ⟨10882881045891229509067691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29021016122376612024180509 10882881045891229509067691)
    ·
      refine ⟨16324321568836844263601537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10882881045891229509067691 16324321568836844263601537)
      ·
        refine ⟨12243241176627633197701153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16324321568836844263601537 12243241176627633197701153)
        ·
          refine ⟨9182430882470724898275865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12243241176627633197701153 9182430882470724898275865)
          ·
            refine ⟨6886823161853043673706899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9182430882470724898275865 6886823161853043673706899)
            ·
              refine ⟨10330234742779565510560349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6886823161853043673706899 10330234742779565510560349)
              ·
                refine ⟨3873838028542337066460131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10330234742779565510560349 3873838028542337066460131)
                ·
                  refine ⟨5810757042813505599690197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3873838028542337066460131 5810757042813505599690197)
                  ·
                    refine ⟨136189618190941537492739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5810757042813505599690197 136189618190941537492739)
                    ·
                      rfl

theorem cell23_795685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 7].length) (baseStart_795685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_795685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_795685 prefixEnd_795685 := by exact prefixLift 795685
  have htrace : WordTrace (prefixWord ++ tailWord_795685) baseStart_795685 baseEnd_795685 := by
    simpa [prefixWord, tailWord_795685, baseEnd_795685] using wordTrace_append hprefix tailTrace_795685
  have hstable : (prefixWord ++ tailWord_795685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795685).length < 2 ^ (prefixWord ++ tailWord_795685).sum := by decide
  have hdescent : baseEnd_795685 < baseStart_795685 := by decide
  rcases family_descends (prefixWord ++ tailWord_795685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795735 : List Nat := [1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 6]
def baseStart_795735 : Nat := 118140960795 + 795735 * 2 ^ 59
def prefixEnd_795735 : Nat := 4983230072969 + 3 ^ 40 * 795735 * 2
def baseEnd_795735 : Nat := 408594528605549416852987

theorem tailTrace_795735 : CollatzResearch.WordTrace tailWord_795735 prefixEnd_795735 408594528605549416852987 := by
  unfold tailWord_795735
  simp only [CollatzResearch.WordTrace]
  refine ⟨29022839772195470563500659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19348559848130313709000439 29022839772195470563500659)
  ·
    refine ⟨43534259658293205845250989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29022839772195470563500659 43534259658293205845250989)
    ·
      refine ⟨16325347371859952191969121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43534259658293205845250989 16325347371859952191969121)
      ·
        refine ⟨12244010528894964143976841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16325347371859952191969121 12244010528894964143976841)
        ·
          refine ⟨9183007896671223107982631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12244010528894964143976841 9183007896671223107982631)
          ·
            refine ⟨13774511845006834661973947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9183007896671223107982631 13774511845006834661973947)
            ·
              refine ⟨20661767767510251992960921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13774511845006834661973947 20661767767510251992960921)
              ·
                refine ⟨15496325825632688994720691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20661767767510251992960921 15496325825632688994720691)
                ·
                  refine ⟨23244488738449033492081037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15496325825632688994720691 23244488738449033492081037)
                  ·
                    refine ⟨8716683276918387559530389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23244488738449033492081037 8716683276918387559530389)
                    ·
                      refine ⟨408594528605549416852987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8716683276918387559530389 408594528605549416852987)
                      ·
                        rfl

theorem cell23_795735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_795735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_795735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_795735 prefixEnd_795735 := by exact prefixLift 795735
  have htrace : WordTrace (prefixWord ++ tailWord_795735) baseStart_795735 baseEnd_795735 := by
    simpa [prefixWord, tailWord_795735, baseEnd_795735] using wordTrace_append hprefix tailTrace_795735
  have hstable : (prefixWord ++ tailWord_795735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795735).length < 2 ^ (prefixWord ++ tailWord_795735).sum := by decide
  have hdescent : baseEnd_795735 < baseStart_795735 := by decide
  rcases family_descends (prefixWord ++ tailWord_795735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795745 : List Nat := [1, 2, 3, 1, 1, 2, 2, 1, 10]
def baseStart_795745 : Nat := 118140960795 + 795745 * 2 ^ 59
def prefixEnd_795745 : Nat := 4983230072969 + 3 ^ 40 * 795745 * 2
def baseEnd_795745 : Nat := 45399962601343819747549

theorem tailTrace_795745 : CollatzResearch.WordTrace tailWord_795745 prefixEnd_795745 45399962601343819747549 := by
  unfold tailWord_795745
  simp only [CollatzResearch.WordTrace]
  refine ⟨29023204502159242271364689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19348803001439494847576459 29023204502159242271364689)
  ·
    refine ⟨21767403376619431703523517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29023204502159242271364689 21767403376619431703523517)
    ·
      refine ⟨8162776266232286888821319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21767403376619431703523517 8162776266232286888821319)
      ·
        refine ⟨12244164399348430333231979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8162776266232286888821319 12244164399348430333231979)
        ·
          refine ⟨18366246599022645499847969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12244164399348430333231979 18366246599022645499847969)
          ·
            refine ⟨13774684949266984124885977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18366246599022645499847969 13774684949266984124885977)
            ·
              refine ⟨10331013711950238093664483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13774684949266984124885977 10331013711950238093664483)
              ·
                refine ⟨15496520567925357140496725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10331013711950238093664483 15496520567925357140496725)
                ·
                  refine ⟨45399962601343819747549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 15496520567925357140496725 45399962601343819747549)
                  ·
                    rfl

theorem cell23_795745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 10].length) (baseStart_795745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_795745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_795745 prefixEnd_795745 := by exact prefixLift 795745
  have htrace : WordTrace (prefixWord ++ tailWord_795745) baseStart_795745 baseEnd_795745 := by
    simpa [prefixWord, tailWord_795745, baseEnd_795745] using wordTrace_append hprefix tailTrace_795745
  have hstable : (prefixWord ++ tailWord_795745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795745).length < 2 ^ (prefixWord ++ tailWord_795745).sum := by decide
  have hdescent : baseEnd_795745 < baseStart_795745 := by decide
  rcases family_descends (prefixWord ++ tailWord_795745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795809 : List Nat := [1, 2, 3, 3, 1, 1, 3, 3, 1, 5]
def baseStart_795809 : Nat := 118140960795 + 795809 * 2 ^ 59
def prefixEnd_795809 : Nat := 4983230072969 + 3 ^ 40 * 795809 * 2
def baseEnd_795809 : Nat := 136210842057994042442549

theorem tailTrace_795809 : CollatzResearch.WordTrace tailWord_795809 prefixEnd_795809 136210842057994042442549 := by
  unfold tailWord_795809
  simp only [CollatzResearch.WordTrace]
  refine ⟨29025538773927381201694481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19350359182618254134462987 29025538773927381201694481)
  ·
    refine ⟨21769154080445535901270861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29025538773927381201694481 21769154080445535901270861)
    ·
      refine ⟨8163432780167075962976573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21769154080445535901270861 8163432780167075962976573)
      ·
        refine ⟨3061287292562653486116215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8163432780167075962976573 3061287292562653486116215)
        ·
          refine ⟨4591930938843980229174323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3061287292562653486116215 4591930938843980229174323)
          ·
            refine ⟨6887896408265970343761485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4591930938843980229174323 6887896408265970343761485)
            ·
              refine ⟨2582961153099738878910557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6887896408265970343761485 2582961153099738878910557)
              ·
                refine ⟨968610432412402079591459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2582961153099738878910557 968610432412402079591459)
                ·
                  refine ⟨1452915648618603119387189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 968610432412402079591459 1452915648618603119387189)
                  ·
                    refine ⟨136210842057994042442549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1452915648618603119387189 136210842057994042442549)
                    ·
                      rfl

theorem cell23_795809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 3, 1, 5].length) (baseStart_795809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_795809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_795809 prefixEnd_795809 := by exact prefixLift 795809
  have htrace : WordTrace (prefixWord ++ tailWord_795809) baseStart_795809 baseEnd_795809 := by
    simpa [prefixWord, tailWord_795809, baseEnd_795809] using wordTrace_append hprefix tailTrace_795809
  have hstable : (prefixWord ++ tailWord_795809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795809).length < 2 ^ (prefixWord ++ tailWord_795809).sum := by decide
  have hdescent : baseEnd_795809 < baseStart_795809 := by decide
  rcases family_descends (prefixWord ++ tailWord_795809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795830 : List Nat := [5, 1, 3, 2, 1, 1, 3, 1, 6]
def baseStart_795830 : Nat := 118140960795 + 795830 * 2 ^ 59
def prefixEnd_795830 : Nat := 4983230072969 + 3 ^ 40 * 795830 * 2
def baseEnd_795830 : Nat := 45404812140858505018339

theorem tailTrace_795830 : CollatzResearch.WordTrace tailWord_795830 prefixEnd_795830 45404812140858505018339 := by
  unfold tailWord_795830
  simp only [CollatzResearch.WordTrace]
  refine ⟨1814144044178206361763059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19350869804567534525472629 1814144044178206361763059)
  ·
    refine ⟨2721216066267309542644589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1814144044178206361763059 2721216066267309542644589)
    ·
      refine ⟨1020456024850241078491721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2721216066267309542644589 1020456024850241078491721)
      ·
        refine ⟨765342018637680808868791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1020456024850241078491721 765342018637680808868791)
        ·
          refine ⟨1148013027956521213303187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 765342018637680808868791 1148013027956521213303187)
          ·
            refine ⟨1722019541934781819954781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1148013027956521213303187 1722019541934781819954781)
            ·
              refine ⟨645757328225543182483043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1722019541934781819954781 645757328225543182483043)
              ·
                refine ⟨968635992338314773724565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 645757328225543182483043 968635992338314773724565)
                ·
                  refine ⟨45404812140858505018339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 968635992338314773724565 45404812140858505018339)
                  ·
                    rfl

theorem cell23_795830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 3, 1, 6].length) (baseStart_795830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_795830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_795830 prefixEnd_795830 := by exact prefixLift 795830
  have htrace : WordTrace (prefixWord ++ tailWord_795830) baseStart_795830 baseEnd_795830 := by
    simpa [prefixWord, tailWord_795830, baseEnd_795830] using wordTrace_append hprefix tailTrace_795830
  have hstable : (prefixWord ++ tailWord_795830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795830).length < 2 ^ (prefixWord ++ tailWord_795830).sum := by decide
  have hdescent : baseEnd_795830 < baseStart_795830 := by decide
  rcases family_descends (prefixWord ++ tailWord_795830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795832 : List Nat := [2, 1, 2, 1, 2, 1, 2, 1, 2, 6, 3]
def baseStart_795832 : Nat := 118140960795 + 795832 * 2 ^ 59
def prefixEnd_795832 : Nat := 4983230072969 + 3 ^ 40 * 795832 * 2
def baseEnd_795832 : Nat := 408644336229035537340041

theorem tailTrace_795832 : CollatzResearch.WordTrace tailWord_795832 prefixEnd_795832 408644336229035537340041 := by
  unfold tailWord_795832
  simp only [CollatzResearch.WordTrace]
  refine ⟨14513188826422028064890875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19350918435229370753187833 14513188826422028064890875)
  ·
    refine ⟨21769783239633042097336313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14513188826422028064890875 21769783239633042097336313)
    ·
      refine ⟨16327337429724781573002235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21769783239633042097336313 16327337429724781573002235)
      ·
        refine ⟨24491006144587172359503353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16327337429724781573002235 24491006144587172359503353)
        ·
          refine ⟨18368254608440379269627515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24491006144587172359503353 18368254608440379269627515)
          ·
            refine ⟨27552381912660568904441273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18368254608440379269627515 27552381912660568904441273)
            ·
              refine ⟨20664286434495426678330955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27552381912660568904441273 20664286434495426678330955)
              ·
                refine ⟨30996429651743140017496433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20664286434495426678330955 30996429651743140017496433)
                ·
                  refine ⟨23247322238807355013122325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30996429651743140017496433 23247322238807355013122325)
                  ·
                    refine ⟨1089718229944094766240109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23247322238807355013122325 1089718229944094766240109)
                    ·
                      refine ⟨408644336229035537340041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1089718229944094766240109 408644336229035537340041)
                      ·
                        rfl

theorem cell23_795832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 6, 3].length) (baseStart_795832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_795832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_795832 prefixEnd_795832 := by exact prefixLift 795832
  have htrace : WordTrace (prefixWord ++ tailWord_795832) baseStart_795832 baseEnd_795832 := by
    simpa [prefixWord, tailWord_795832, baseEnd_795832] using wordTrace_append hprefix tailTrace_795832
  have hstable : (prefixWord ++ tailWord_795832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795832).length < 2 ^ (prefixWord ++ tailWord_795832).sum := by decide
  have hdescent : baseEnd_795832 < baseStart_795832 := by decide
  rcases family_descends (prefixWord ++ tailWord_795832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795839 : List Nat := [1, 1, 2, 2, 2, 2, 2, 5, 2, 4]
def baseStart_795839 : Nat := 118140960795 + 795839 * 2 ^ 59
def prefixEnd_795839 : Nat := 4983230072969 + 3 ^ 40 * 795839 * 2
def baseEnd_795839 : Nat := 136215976864539003317503

theorem tailTrace_795839 : CollatzResearch.WordTrace tailWord_795839 prefixEnd_795839 136215976864539003317503 := by
  unfold tailWord_795839
  simp only [CollatzResearch.WordTrace]
  refine ⟨29026632963818696325286571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19351088642545797550191047 29026632963818696325286571)
  ·
    refine ⟨43539949445728044487929857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29026632963818696325286571 43539949445728044487929857)
    ·
      refine ⟨32654962084296033365947393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43539949445728044487929857 32654962084296033365947393)
      ·
        refine ⟨24491221563222025024460545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32654962084296033365947393 24491221563222025024460545)
        ·
          refine ⟨18368416172416518768345409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24491221563222025024460545 18368416172416518768345409)
          ·
            refine ⟨13776312129312389076259057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18368416172416518768345409 13776312129312389076259057)
            ·
              refine ⟨10332234096984291807194293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13776312129312389076259057 10332234096984291807194293)
              ·
                refine ⟨968646946592277356924465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10332234096984291807194293 968646946592277356924465)
                ·
                  refine ⟨726485209944208017693349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 968646946592277356924465 726485209944208017693349)
                  ·
                    refine ⟨136215976864539003317503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 726485209944208017693349 136215976864539003317503)
                    ·
                      rfl

theorem cell23_795839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 5, 2, 4].length) (baseStart_795839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_795839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_795839 prefixEnd_795839 := by exact prefixLift 795839
  have htrace : WordTrace (prefixWord ++ tailWord_795839) baseStart_795839 baseEnd_795839 := by
    simpa [prefixWord, tailWord_795839, baseEnd_795839] using wordTrace_append hprefix tailTrace_795839
  have hstable : (prefixWord ++ tailWord_795839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795839).length < 2 ^ (prefixWord ++ tailWord_795839).sum := by decide
  have hdescent : baseEnd_795839 < baseStart_795839 := by decide
  rcases family_descends (prefixWord ++ tailWord_795839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795889 : List Nat := [1, 2, 2, 2, 2, 1, 1, 1, 2, 7, 2]
def baseStart_795889 : Nat := 118140960795 + 795889 * 2 ^ 59
def prefixEnd_795889 : Nat := 4983230072969 + 3 ^ 40 * 795889 * 2
def baseEnd_795889 : Nat := 408673604626341814327279

theorem tailTrace_795889 : CollatzResearch.WordTrace tailWord_795889 prefixEnd_795889 408673604626341814327279 := by
  unfold tailWord_795889
  simp only [CollatzResearch.WordTrace]
  refine ⟨29028456613637554864606721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19352304409091703243071147 29028456613637554864606721)
  ·
    refine ⟨21771342460228166148455041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29028456613637554864606721 21771342460228166148455041)
    ·
      refine ⟨16328506845171124611341281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21771342460228166148455041 16328506845171124611341281)
      ·
        refine ⟨12246380133878343458505961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16328506845171124611341281 12246380133878343458505961)
        ·
          refine ⟨9184785100408757593879471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12246380133878343458505961 9184785100408757593879471)
          ·
            refine ⟨13777177650613136390819207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9184785100408757593879471 13777177650613136390819207)
            ·
              refine ⟨20665766475919704586228811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13777177650613136390819207 20665766475919704586228811)
              ·
                refine ⟨30998649713879556879343217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20665766475919704586228811 30998649713879556879343217)
                ·
                  refine ⟨23248987285409667659507413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30998649713879556879343217 23248987285409667659507413)
                  ·
                    refine ⟨544898139501789085769705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23248987285409667659507413 544898139501789085769705)
                    ·
                      refine ⟨408673604626341814327279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 544898139501789085769705 408673604626341814327279)
                      ·
                        rfl

theorem cell23_795889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 7, 2].length) (baseStart_795889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_795889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_795889 prefixEnd_795889 := by exact prefixLift 795889
  have htrace : WordTrace (prefixWord ++ tailWord_795889) baseStart_795889 baseEnd_795889 := by
    simpa [prefixWord, tailWord_795889, baseEnd_795889] using wordTrace_append hprefix tailTrace_795889
  have hstable : (prefixWord ++ tailWord_795889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795889).length < 2 ^ (prefixWord ++ tailWord_795889).sum := by decide
  have hdescent : baseEnd_795889 < baseStart_795889 := by decide
  rcases family_descends (prefixWord ++ tailWord_795889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795890 : List Nat := [3, 2, 1, 3, 3, 2, 2, 1, 2, 4]
def baseStart_795890 : Nat := 118140960795 + 795890 * 2 ^ 59
def prefixEnd_795890 : Nat := 4983230072969 + 3 ^ 40 * 795890 * 2
def baseEnd_795890 : Nat := 136224706035665436804925

theorem tailTrace_795890 : CollatzResearch.WordTrace tailWord_795890 prefixEnd_795890 136224706035665436804925 := by
  unfold tailWord_795890
  simp only [CollatzResearch.WordTrace]
  refine ⟨7257123271658483008848281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19352328724422621356928749 7257123271658483008848281)
  ·
    refine ⟨5442842453743862256636211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7257123271658483008848281 5442842453743862256636211)
    ·
      refine ⟨8164263680615793384954317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5442842453743862256636211 8164263680615793384954317)
      ·
        refine ⟨3061598880230922519357869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8164263680615793384954317 3061598880230922519357869)
        ·
          refine ⟨1148099580086595944759201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3061598880230922519357869 1148099580086595944759201)
          ·
            refine ⟨861074685064946958569401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1148099580086595944759201 861074685064946958569401)
            ·
              refine ⟨645806013798710218927051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 861074685064946958569401 645806013798710218927051)
              ·
                refine ⟨968709020698065328390577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 645806013798710218927051 968709020698065328390577)
                ·
                  refine ⟨726531765523548996292933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 968709020698065328390577 726531765523548996292933)
                  ·
                    refine ⟨136224706035665436804925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 726531765523548996292933 136224706035665436804925)
                    ·
                      rfl

theorem cell23_795890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 2, 1, 2, 4].length) (baseStart_795890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_795890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_795890 prefixEnd_795890 := by exact prefixLift 795890
  have htrace : WordTrace (prefixWord ++ tailWord_795890) baseStart_795890 baseEnd_795890 := by
    simpa [prefixWord, tailWord_795890, baseEnd_795890] using wordTrace_append hprefix tailTrace_795890
  have hstable : (prefixWord ++ tailWord_795890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795890).length < 2 ^ (prefixWord ++ tailWord_795890).sum := by decide
  have hdescent : baseEnd_795890 < baseStart_795890 := by decide
  rcases family_descends (prefixWord ++ tailWord_795890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795900 : List Nat := [2, 2, 2, 1, 6, 1, 1, 2, 1, 2, 3]
def baseStart_795900 : Nat := 118140960795 + 795900 * 2 ^ 59
def prefixEnd_795900 : Nat := 4983230072969 + 3 ^ 40 * 795900 * 2
def baseEnd_795900 : Nat := 408679252913541271289729

theorem tailTrace_795900 : CollatzResearch.WordTrace tailWord_795900 prefixEnd_795900 408679252913541271289729 := by
  unfold tailWord_795900
  simp only [CollatzResearch.WordTrace]
  refine ⟨14514428908298851871628577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19352571877731802495504769 14514428908298851871628577)
  ·
    refine ⟨10885821681224138903721433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14514428908298851871628577 10885821681224138903721433)
    ·
      refine ⟨8164366260918104177791075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10885821681224138903721433 8164366260918104177791075)
      ·
        refine ⟨12246549391377156266686613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8164366260918104177791075 12246549391377156266686613)
        ·
          refine ⟨574057002720804200000935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12246549391377156266686613 574057002720804200000935)
          ·
            refine ⟨861085504081206300001403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 574057002720804200000935 861085504081206300001403)
            ·
              refine ⟨1291628256121809450002105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 861085504081206300001403 1291628256121809450002105)
              ·
                refine ⟨968721192091357087501579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1291628256121809450002105 968721192091357087501579)
                ·
                  refine ⟨1453081788137035631252369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 968721192091357087501579 1453081788137035631252369)
                  ·
                    refine ⟨1089811341102776723439277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1453081788137035631252369 1089811341102776723439277)
                    ·
                      refine ⟨408679252913541271289729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1089811341102776723439277 408679252913541271289729)
                      ·
                        rfl

theorem cell23_795900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 2, 1, 2, 3].length) (baseStart_795900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_795900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_795900 prefixEnd_795900 := by exact prefixLift 795900
  have htrace : WordTrace (prefixWord ++ tailWord_795900) baseStart_795900 baseEnd_795900 := by
    simpa [prefixWord, tailWord_795900, baseEnd_795900] using wordTrace_append hprefix tailTrace_795900
  have hstable : (prefixWord ++ tailWord_795900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795900).length < 2 ^ (prefixWord ++ tailWord_795900).sum := by decide
  have hdescent : baseEnd_795900 < baseStart_795900 := by decide
  rcases family_descends (prefixWord ++ tailWord_795900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795939 : List Nat := [1, 1, 1, 4, 2, 3, 1, 1, 2, 4, 3]
def baseStart_795939 : Nat := 118140960795 + 795939 * 2 ^ 59
def prefixEnd_795939 : Nat := 4983230072969 + 3 ^ 40 * 795939 * 2
def baseEnd_795939 : Nat := 408699278659066618702049

theorem tailTrace_795939 : CollatzResearch.WordTrace tailWord_795939 prefixEnd_795939 408699278659066618702049 := by
  unfold tailWord_795939
  simp only [CollatzResearch.WordTrace]
  refine ⟨29030280263456413403926871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19353520175637608935951247 29030280263456413403926871)
  ·
    refine ⟨43545420395184620105890307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29030280263456413403926871 43545420395184620105890307)
    ·
      refine ⟨65318130592776930158835461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43545420395184620105890307 65318130592776930158835461)
      ·
        refine ⟨12247149486145674404781649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65318130592776930158835461 12247149486145674404781649)
        ·
          refine ⟨9185362114609255803586237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12247149486145674404781649 9185362114609255803586237)
          ·
            refine ⟨3444510792978470926344839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9185362114609255803586237 3444510792978470926344839)
            ·
              refine ⟨5166766189467706389517259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3444510792978470926344839 5166766189467706389517259)
              ·
                refine ⟨7750149284201559584275889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5166766189467706389517259 7750149284201559584275889)
                ·
                  refine ⟨5812611963151169688206917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7750149284201559584275889 5812611963151169688206917)
                  ·
                    refine ⟨1089864743090844316538797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5812611963151169688206917 1089864743090844316538797)
                    ·
                      refine ⟨408699278659066618702049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1089864743090844316538797 408699278659066618702049)
                      ·
                        rfl

theorem cell23_795939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 4, 3].length) (baseStart_795939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_795939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_795939 prefixEnd_795939 := by exact prefixLift 795939
  have htrace : WordTrace (prefixWord ++ tailWord_795939) baseStart_795939 baseEnd_795939 := by
    simpa [prefixWord, tailWord_795939, baseEnd_795939] using wordTrace_append hprefix tailTrace_795939
  have hstable : (prefixWord ++ tailWord_795939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795939).length < 2 ^ (prefixWord ++ tailWord_795939).sum := by decide
  have hdescent : baseEnd_795939 < baseStart_795939 := by decide
  rcases family_descends (prefixWord ++ tailWord_795939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795946 : List Nat := [3, 1, 4, 2, 1, 2, 1, 1, 2, 6]
def baseStart_795946 : Nat := 118140960795 + 795946 * 2 ^ 59
def prefixEnd_795946 : Nat := 4983230072969 + 3 ^ 40 * 795946 * 2
def baseEnd_795946 : Nat := 136234291007882697104839

theorem tailTrace_795946 : CollatzResearch.WordTrace tailWord_795946 prefixEnd_795946 136234291007882697104839 := by
  unfold tailWord_795946
  simp only [CollatzResearch.WordTrace]
  refine ⟨7257633893607763399857923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19353690382954035732954461 7257633893607763399857923)
  ·
    refine ⟨10886450840411645099786885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7257633893607763399857923 10886450840411645099786885)
    ·
      refine ⟨2041209532577183456210041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10886450840411645099786885 2041209532577183456210041)
      ·
        refine ⟨1530907149432887592157531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2041209532577183456210041 1530907149432887592157531)
        ·
          refine ⟨2296360724149331388236297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1530907149432887592157531 2296360724149331388236297)
          ·
            refine ⟨1722270543111998541177223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2296360724149331388236297 1722270543111998541177223)
            ·
              refine ⟨2583405814667997811765835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1722270543111998541177223 2583405814667997811765835)
              ·
                refine ⟨3875108722001996717648753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2583405814667997811765835 3875108722001996717648753)
                ·
                  refine ⟨2906331541501497538236565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3875108722001996717648753 2906331541501497538236565)
                  ·
                    refine ⟨136234291007882697104839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2906331541501497538236565 136234291007882697104839)
                    ·
                      rfl

theorem cell23_795946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_795946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_795946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_795946 prefixEnd_795946 := by exact prefixLift 795946
  have htrace : WordTrace (prefixWord ++ tailWord_795946) baseStart_795946 baseEnd_795946 := by
    simpa [prefixWord, tailWord_795946, baseEnd_795946] using wordTrace_append hprefix tailTrace_795946
  have hstable : (prefixWord ++ tailWord_795946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795946).length < 2 ^ (prefixWord ++ tailWord_795946).sum := by decide
  have hdescent : baseEnd_795946 < baseStart_795946 := by decide
  rcases family_descends (prefixWord ++ tailWord_795946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795953 : List Nat := [1, 2, 2, 3, 3, 2, 2, 1, 1, 4, 2]
def baseStart_795953 : Nat := 118140960795 + 795953 * 2 ^ 59
def prefixEnd_795953 : Nat := 4983230072969 + 3 ^ 40 * 795953 * 2
def baseEnd_795953 : Nat := 408706467388229563926985

theorem tailTrace_795953 : CollatzResearch.WordTrace tailWord_795953 prefixEnd_795953 408706467388229563926985 := by
  unfold tailWord_795953
  simp only [CollatzResearch.WordTrace]
  refine ⟨29030790885405693794936513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19353860590270462529957675 29030790885405693794936513)
  ·
    refine ⟨21773093164054270346202385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29030790885405693794936513 21773093164054270346202385)
    ·
      refine ⟨16329819873040702759651789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21773093164054270346202385 16329819873040702759651789)
      ·
        refine ⟨6123682452390263534869421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16329819873040702759651789 6123682452390263534869421)
        ·
          refine ⟨2296380919646348825576033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6123682452390263534869421 2296380919646348825576033)
          ·
            refine ⟨1722285689734761619182025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2296380919646348825576033 1722285689734761619182025)
            ·
              refine ⟨1291714267301071214386519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1722285689734761619182025 1291714267301071214386519)
              ·
                refine ⟨1937571400951606821579779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1291714267301071214386519 1937571400951606821579779)
                ·
                  refine ⟨2906357101427410232369669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1937571400951606821579779 2906357101427410232369669)
                  ·
                    refine ⟨544941956517639418569313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2906357101427410232369669 544941956517639418569313)
                    ·
                      refine ⟨408706467388229563926985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 544941956517639418569313 408706467388229563926985)
                      ·
                        rfl

theorem cell23_795953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 1, 1, 4, 2].length) (baseStart_795953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_795953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_795953 prefixEnd_795953 := by exact prefixLift 795953
  have htrace : WordTrace (prefixWord ++ tailWord_795953) baseStart_795953 baseEnd_795953 := by
    simpa [prefixWord, tailWord_795953, baseEnd_795953] using wordTrace_append hprefix tailTrace_795953
  have hstable : (prefixWord ++ tailWord_795953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795953).length < 2 ^ (prefixWord ++ tailWord_795953).sum := by decide
  have hdescent : baseEnd_795953 < baseStart_795953 := by decide
  rcases family_descends (prefixWord ++ tailWord_795953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795956 : List Nat := [2, 5, 1, 1, 1, 1, 1, 2, 2, 4, 3]
def baseStart_795956 : Nat := 118140960795 + 795956 * 2 ^ 59
def prefixEnd_795956 : Nat := 4983230072969 + 3 ^ 40 * 795956 * 2
def baseEnd_795956 : Nat := 408708007830193052189471

theorem tailTrace_795956 : CollatzResearch.WordTrace tailWord_795956 prefixEnd_795956 408708007830193052189471 := by
  unfold tailWord_795956
  simp only [CollatzResearch.WordTrace]
  refine ⟨14515450152197412653647861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19353933536263216871530481 14515450152197412653647861)
  ·
    refine ⟨1360823451768507436279487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14515450152197412653647861 1360823451768507436279487)
    ·
      refine ⟨2041235177652761154419231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1360823451768507436279487 2041235177652761154419231)
      ·
        refine ⟨3061852766479141731628847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2041235177652761154419231 3061852766479141731628847)
        ·
          refine ⟨4592779149718712597443271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3061852766479141731628847 4592779149718712597443271)
          ·
            refine ⟨6889168724578068896164907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4592779149718712597443271 6889168724578068896164907)
            ·
              refine ⟨10333753086867103344247361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6889168724578068896164907 10333753086867103344247361)
              ·
                refine ⟨7750314815150327508185521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10333753086867103344247361 7750314815150327508185521)
                ·
                  refine ⟨5812736111362745631139141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7750314815150327508185521 5812736111362745631139141)
                  ·
                    refine ⟨1089888020880514805838589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5812736111362745631139141 1089888020880514805838589)
                    ·
                      refine ⟨408708007830193052189471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1089888020880514805838589 408708007830193052189471)
                      ·
                        rfl

theorem cell23_795956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_795956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_795956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_795956 prefixEnd_795956 := by exact prefixLift 795956
  have htrace : WordTrace (prefixWord ++ tailWord_795956) baseStart_795956 baseEnd_795956 := by
    simpa [prefixWord, tailWord_795956, baseEnd_795956] using wordTrace_append hprefix tailTrace_795956
  have hstable : (prefixWord ++ tailWord_795956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795956).length < 2 ^ (prefixWord ++ tailWord_795956).sum := by decide
  have hdescent : baseEnd_795956 < baseStart_795956 := by decide
  rcases family_descends (prefixWord ++ tailWord_795956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795974 : List Nat := [6, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2]
def baseStart_795974 : Nat := 118140960795 + 795974 * 2 ^ 59
def prefixEnd_795974 : Nat := 4983230072969 + 3 ^ 40 * 795974 * 2
def baseEnd_795974 : Nat := 408717250481973981764389

theorem tailTrace_795974 : CollatzResearch.WordTrace tailWord_795974 prefixEnd_795974 408717250481973981764389 := by
  unfold tailWord_795974
  simp only [CollatzResearch.WordTrace]
  refine ⟨907236150572800449420343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19354371212219742920967317 907236150572800449420343)
  ·
    refine ⟨1360854225859200674130515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 907236150572800449420343 1360854225859200674130515)
    ·
      refine ⟨2041281338788801011195773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1360854225859200674130515 2041281338788801011195773)
      ·
        refine ⟨765480502045800379198415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2041281338788801011195773 765480502045800379198415)
        ·
          refine ⟨1148220753068700568797623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 765480502045800379198415 1148220753068700568797623)
          ·
            refine ⟨1722331129603050853196435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1148220753068700568797623 1722331129603050853196435)
            ·
              refine ⟨2583496694404576279794653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1722331129603050853196435 2583496694404576279794653)
              ·
                refine ⟨968811260401716104922995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2583496694404576279794653 968811260401716104922995)
                ·
                  refine ⟨1453216890602574157384493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 968811260401716104922995 1453216890602574157384493)
                  ·
                    refine ⟨544956333975965309019185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1453216890602574157384493 544956333975965309019185)
                    ·
                      refine ⟨408717250481973981764389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 544956333975965309019185 408717250481973981764389)
                      ·
                        rfl

theorem cell23_795974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_795974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_795974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_795974 prefixEnd_795974 := by exact prefixLift 795974
  have htrace : WordTrace (prefixWord ++ tailWord_795974) baseStart_795974 baseEnd_795974 := by
    simpa [prefixWord, tailWord_795974, baseEnd_795974] using wordTrace_append hprefix tailTrace_795974
  have hstable : (prefixWord ++ tailWord_795974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795974).length < 2 ^ (prefixWord ++ tailWord_795974).sum := by decide
  have hdescent : baseEnd_795974 < baseStart_795974 := by decide
  rcases family_descends (prefixWord ++ tailWord_795974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796009 : List Nat := [1, 2, 1, 1, 1, 3, 2, 1, 6, 1, 4]
def baseStart_796009 : Nat := 118140960795 + 796009 * 2 ^ 59
def prefixEnd_796009 : Nat := 4983230072969 + 3 ^ 40 * 796009 * 2
def baseEnd_796009 : Nat := 408735222304881344826727

theorem tailTrace_796009 : CollatzResearch.WordTrace tailWord_796009 prefixEnd_796009 408735222304881344826727 := by
  unfold tailWord_796009
  simp only [CollatzResearch.WordTrace]
  refine ⟨29032833373202815358975081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19355222248801876905983387 29032833373202815358975081)
  ·
    refine ⟨21774625029902111519231311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29032833373202815358975081 21774625029902111519231311)
    ·
      refine ⟨32661937544853167278846967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21774625029902111519231311 32661937544853167278846967)
      ·
        refine ⟨48992906317279750918270451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32661937544853167278846967 48992906317279750918270451)
        ·
          refine ⟨73489359475919626377405677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48992906317279750918270451 73489359475919626377405677)
          ·
            refine ⟨27558509803469859891527129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73489359475919626377405677 27558509803469859891527129)
            ·
              refine ⟨20668882352602394918645347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27558509803469859891527129 20668882352602394918645347)
              ·
                refine ⟨31003323528903592377968021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20668882352602394918645347 31003323528903592377968021)
                ·
                  refine ⟨1453280790417355892717251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 31003323528903592377968021 1453280790417355892717251)
                  ·
                    refine ⟨2179921185626033839075877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1453280790417355892717251 2179921185626033839075877)
                    ·
                      refine ⟨408735222304881344826727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2179921185626033839075877 408735222304881344826727)
                      ·
                        rfl

theorem cell23_796009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 6, 1, 4].length) (baseStart_796009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_796009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_796009 prefixEnd_796009 := by exact prefixLift 796009
  have htrace : WordTrace (prefixWord ++ tailWord_796009) baseStart_796009 baseEnd_796009 := by
    simpa [prefixWord, tailWord_796009, baseEnd_796009] using wordTrace_append hprefix tailTrace_796009
  have hstable : (prefixWord ++ tailWord_796009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796009).length < 2 ^ (prefixWord ++ tailWord_796009).sum := by decide
  have hdescent : baseEnd_796009 < baseStart_796009 := by decide
  rcases family_descends (prefixWord ++ tailWord_796009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796053 : List Nat := [1, 3, 2, 1, 1, 2, 2, 6, 1, 4]
def baseStart_796053 : Nat := 118140960795 + 796053 * 2 ^ 59
def prefixEnd_796053 : Nat := 4983230072969 + 3 ^ 40 * 796053 * 2
def baseEnd_796053 : Nat := 136252605151226390892175

theorem tailTrace_796053 : CollatzResearch.WordTrace tailWord_796053 prefixEnd_796053 136252605151226390892175 := by
  unfold tailWord_796053
  simp only [CollatzResearch.WordTrace]
  refine ⟨29034438185043410873576813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19356292123362273915717875 29034438185043410873576813)
  ·
    refine ⟨10887914319391279077591305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29034438185043410873576813 10887914319391279077591305)
    ·
      refine ⟨8165935739543459308193479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10887914319391279077591305 8165935739543459308193479)
      ·
        refine ⟨12248903609315188962290219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8165935739543459308193479 12248903609315188962290219)
        ·
          refine ⟨18373355413972783443435329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12248903609315188962290219 18373355413972783443435329)
          ·
            refine ⟨13780016560479587582576497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18373355413972783443435329 13780016560479587582576497)
            ·
              refine ⟨10335012420359690686932373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13780016560479587582576497 10335012420359690686932373)
              ·
                refine ⟨484453707204360500949955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10335012420359690686932373 484453707204360500949955)
                ·
                  refine ⟨726680560806540751424933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 484453707204360500949955 726680560806540751424933)
                  ·
                    refine ⟨136252605151226390892175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 726680560806540751424933 136252605151226390892175)
                    ·
                      rfl

theorem cell23_796053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 6, 1, 4].length) (baseStart_796053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_796053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_796053 prefixEnd_796053 := by exact prefixLift 796053
  have htrace : WordTrace (prefixWord ++ tailWord_796053) baseStart_796053 baseEnd_796053 := by
    simpa [prefixWord, tailWord_796053, baseEnd_796053] using wordTrace_append hprefix tailTrace_796053
  have hstable : (prefixWord ++ tailWord_796053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796053).length < 2 ^ (prefixWord ++ tailWord_796053).sum := by decide
  have hdescent : baseEnd_796053 < baseStart_796053 := by decide
  rcases family_descends (prefixWord ++ tailWord_796053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796096 : List Nat := [2, 1, 1, 2, 3, 1, 2, 5, 1, 5]
def baseStart_796096 : Nat := 118140960795 + 796096 * 2 ^ 59
def prefixEnd_796096 : Nat := 4983230072969 + 3 ^ 40 * 796096 * 2
def baseEnd_796096 : Nat := 136259965040607501479609

theorem tailTrace_796096 : CollatzResearch.WordTrace tailWord_796096 prefixEnd_796096 136259965040607501479609 := by
  unfold tailWord_796096
  simp only [CollatzResearch.WordTrace]
  refine ⟨14518003261943814608696071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19357337682591752811594761 14518003261943814608696071)
  ·
    refine ⟨21777004892915721913044107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14518003261943814608696071 21777004892915721913044107)
    ·
      refine ⟨32665507339373582869566161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21777004892915721913044107 32665507339373582869566161)
      ·
        refine ⟨24499130504530187152174621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32665507339373582869566161 24499130504530187152174621)
        ·
          refine ⟨9187173939198820182065483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24499130504530187152174621 9187173939198820182065483)
          ·
            refine ⟨13780760908798230273098225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9187173939198820182065483 13780760908798230273098225)
            ·
              refine ⟨10335570681598672704823669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13780760908798230273098225 10335570681598672704823669)
              ·
                refine ⟨968959751399875566077219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10335570681598672704823669 968959751399875566077219)
                ·
                  refine ⟨1453439627099813349115829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 968959751399875566077219 1453439627099813349115829)
                  ·
                    refine ⟨136259965040607501479609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1453439627099813349115829 136259965040607501479609)
                    ·
                      rfl

theorem cell23_796096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 5, 1, 5].length) (baseStart_796096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_796096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_796096 prefixEnd_796096 := by exact prefixLift 796096
  have htrace : WordTrace (prefixWord ++ tailWord_796096) baseStart_796096 baseEnd_796096 := by
    simpa [prefixWord, tailWord_796096, baseEnd_796096] using wordTrace_append hprefix tailTrace_796096
  have hstable : (prefixWord ++ tailWord_796096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796096).length < 2 ^ (prefixWord ++ tailWord_796096).sum := by decide
  have hdescent : baseEnd_796096 < baseStart_796096 := by decide
  rcases family_descends (prefixWord ++ tailWord_796096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796103 : List Nat := [1, 1, 4, 1, 1, 3, 1, 4, 2, 3, 2]
def baseStart_796103 : Nat := 118140960795 + 796103 * 2 ^ 59
def prefixEnd_796103 : Nat := 4983230072969 + 3 ^ 40 * 796103 * 2
def baseEnd_796103 : Nat := 408783489486403977051295

theorem tailTrace_796103 : CollatzResearch.WordTrace tailWord_796103 prefixEnd_796103 408783489486403977051295 := by
  unfold tailWord_796103
  simp only [CollatzResearch.WordTrace]
  refine ⟨29036261834862269412896963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19357507889908179608597975 29036261834862269412896963)
  ·
    refine ⟨43554392752293404119345445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29036261834862269412896963 43554392752293404119345445)
    ·
      refine ⟨8166448641055013272377271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43554392752293404119345445 8166448641055013272377271)
      ·
        refine ⟨12249672961582519908565907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8166448641055013272377271 12249672961582519908565907)
        ·
          refine ⟨18374509442373779862848861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12249672961582519908565907 18374509442373779862848861)
          ·
            refine ⟨6890441040890167448568323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18374509442373779862848861 6890441040890167448568323)
            ·
              refine ⟨10335661561335251172852485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6890441040890167448568323 10335661561335251172852485)
              ·
                refine ⟨1937936542750359594909841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10335661561335251172852485 1937936542750359594909841)
                ·
                  refine ⟨1453452407062769696182381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1937936542750359594909841 1453452407062769696182381)
                  ·
                    refine ⟨545044652648538636068393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1453452407062769696182381 545044652648538636068393)
                    ·
                      refine ⟨408783489486403977051295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 545044652648538636068393 408783489486403977051295)
                      ·
                        rfl

theorem cell23_796103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 4, 2, 3, 2].length) (baseStart_796103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_796103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_796103 prefixEnd_796103 := by exact prefixLift 796103
  have htrace : WordTrace (prefixWord ++ tailWord_796103) baseStart_796103 baseEnd_796103 := by
    simpa [prefixWord, tailWord_796103, baseEnd_796103] using wordTrace_append hprefix tailTrace_796103
  have hstable : (prefixWord ++ tailWord_796103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796103).length < 2 ^ (prefixWord ++ tailWord_796103).sum := by decide
  have hdescent : baseEnd_796103 < baseStart_796103 := by decide
  rcases family_descends (prefixWord ++ tailWord_796103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796133 : List Nat := [1, 3, 1, 5, 1, 1, 2, 1, 3, 1, 4]
def baseStart_796133 : Nat := 118140960795 + 796133 * 2 ^ 59
def prefixEnd_796133 : Nat := 4983230072969 + 3 ^ 40 * 796133 * 2
def baseEnd_796133 : Nat := 408798893906038859676157

theorem tailTrace_796133 : CollatzResearch.WordTrace tailWord_796133 prefixEnd_796133 408798893906038859676157 := by
  unfold tailWord_796133
  simp only [CollatzResearch.WordTrace]
  refine ⟨29037356024753584536489053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19358237349835723024326035 29037356024753584536489053)
  ·
    refine ⟨10889008509282594201183395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29037356024753584536489053 10889008509282594201183395)
    ·
      refine ⟨16333512763923891301775093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10889008509282594201183395 16333512763923891301775093)
      ·
        refine ⟨1531266821617864809541415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16333512763923891301775093 1531266821617864809541415)
        ·
          refine ⟨2296900232426797214312123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1531266821617864809541415 2296900232426797214312123)
          ·
            refine ⟨3445350348640195821468185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2296900232426797214312123 3445350348640195821468185)
            ·
              refine ⟨2584012761480146866101139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3445350348640195821468185 2584012761480146866101139)
              ·
                refine ⟨3876019142220220299151709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2584012761480146866101139 3876019142220220299151709)
                ·
                  refine ⟨1453507178332582612181891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3876019142220220299151709 1453507178332582612181891)
                  ·
                    refine ⟨2180260767498873918272837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1453507178332582612181891 2180260767498873918272837)
                    ·
                      refine ⟨408798893906038859676157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2180260767498873918272837 408798893906038859676157)
                      ·
                        rfl

theorem cell23_796133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_796133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_796133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_796133 prefixEnd_796133 := by exact prefixLift 796133
  have htrace : WordTrace (prefixWord ++ tailWord_796133) baseStart_796133 baseEnd_796133 := by
    simpa [prefixWord, tailWord_796133, baseEnd_796133] using wordTrace_append hprefix tailTrace_796133
  have hstable : (prefixWord ++ tailWord_796133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796133).length < 2 ^ (prefixWord ++ tailWord_796133).sum := by decide
  have hdescent : baseEnd_796133 < baseStart_796133 := by decide
  rcases family_descends (prefixWord ++ tailWord_796133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796150 : List Nat := [5, 1, 1, 1, 2, 3, 1, 3, 1, 1, 4]
def baseStart_796150 : Nat := 118140960795 + 796150 * 2 ^ 59
def prefixEnd_796150 : Nat := 4983230072969 + 3 ^ 40 * 796150 * 2
def baseEnd_796150 : Nat := 408807623077165293163579

theorem tailTrace_796150 : CollatzResearch.WordTrace tailWord_796150 prefixEnd_796150 408807623077165293163579 := by
  unfold tailWord_796150
  simp only [CollatzResearch.WordTrace]
  refine ⟨1814873504105749777491119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19358650710461330959905269 1814873504105749777491119)
  ·
    refine ⟨2722310256158624666236679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1814873504105749777491119 2722310256158624666236679)
    ·
      refine ⟨4083465384237936999355019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2722310256158624666236679 4083465384237936999355019)
      ·
        refine ⟨6125198076356905499032529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4083465384237936999355019 6125198076356905499032529)
        ·
          refine ⟨4593898557267679124274397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6125198076356905499032529 4593898557267679124274397)
          ·
            refine ⟨1722711958975379671602899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4593898557267679124274397 1722711958975379671602899)
            ·
              refine ⟨2584067938463069507404349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1722711958975379671602899 2584067938463069507404349)
              ·
                refine ⟨969025476923651065276631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2584067938463069507404349 969025476923651065276631)
                ·
                  refine ⟨1453538215385476597914947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 969025476923651065276631 1453538215385476597914947)
                  ·
                    refine ⟨2180307323078214896872421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1453538215385476597914947 2180307323078214896872421)
                    ·
                      refine ⟨408807623077165293163579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2180307323078214896872421 408807623077165293163579)
                      ·
                        rfl

theorem cell23_796150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 3, 1, 1, 4].length) (baseStart_796150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_796150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_796150 prefixEnd_796150 := by exact prefixLift 796150
  have htrace : WordTrace (prefixWord ++ tailWord_796150) baseStart_796150 baseEnd_796150 := by
    simpa [prefixWord, tailWord_796150, baseEnd_796150] using wordTrace_append hprefix tailTrace_796150
  have hstable : (prefixWord ++ tailWord_796150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796150).length < 2 ^ (prefixWord ++ tailWord_796150).sum := by decide
  have hdescent : baseEnd_796150 < baseStart_796150 := by decide
  rcases family_descends (prefixWord ++ tailWord_796150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796167 : List Nat := [1, 1, 4, 3, 2, 2, 2, 1, 3, 2, 2]
def baseStart_796167 : Nat := 118140960795 + 796167 * 2 ^ 59
def prefixEnd_796167 : Nat := 4983230072969 + 3 ^ 40 * 796167 * 2
def baseEnd_796167 : Nat := 408816352248291726651001

theorem tailTrace_796167 : CollatzResearch.WordTrace tailWord_796167 prefixEnd_796167 408816352248291726651001 := by
  unfold tailWord_796167
  simp only [CollatzResearch.WordTrace]
  refine ⟨29038596106630408343226755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19359064071086938895484503 29038596106630408343226755)
  ·
    refine ⟨43557894159945612514840133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29038596106630408343226755 43557894159945612514840133)
    ·
      refine ⟨8167105154989802346532525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43557894159945612514840133 8167105154989802346532525)
      ·
        refine ⟨3062664433121175879949697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8167105154989802346532525 3062664433121175879949697)
        ·
          refine ⟨2296998324840881909962273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3062664433121175879949697 2296998324840881909962273)
          ·
            refine ⟨1722748743630661432471705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2296998324840881909962273 1722748743630661432471705)
            ·
              refine ⟨1292061557722996074353779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1722748743630661432471705 1292061557722996074353779)
              ·
                refine ⟨1938092336584494111530669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1292061557722996074353779 1938092336584494111530669)
                ·
                  refine ⟨726784626219185291824001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1938092336584494111530669 726784626219185291824001)
                  ·
                    refine ⟨545088469664388968868001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 726784626219185291824001 545088469664388968868001)
                    ·
                      refine ⟨408816352248291726651001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 545088469664388968868001 408816352248291726651001)
                      ·
                        rfl

theorem cell23_796167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_796167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_796167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_796167 prefixEnd_796167 := by exact prefixLift 796167
  have htrace : WordTrace (prefixWord ++ tailWord_796167) baseStart_796167 baseEnd_796167 := by
    simpa [prefixWord, tailWord_796167, baseEnd_796167] using wordTrace_append hprefix tailTrace_796167
  have hstable : (prefixWord ++ tailWord_796167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796167).length < 2 ^ (prefixWord ++ tailWord_796167).sum := by decide
  have hdescent : baseEnd_796167 < baseStart_796167 := by decide
  rcases family_descends (prefixWord ++ tailWord_796167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796180 : List Nat := [2, 4, 3, 1, 2, 1, 1, 1, 1, 1, 6]
def baseStart_796180 : Nat := 118140960795 + 796180 * 2 ^ 59
def prefixEnd_796180 : Nat := 4983230072969 + 3 ^ 40 * 796180 * 2
def baseEnd_796180 : Nat := 408823027496800175788441

theorem tailTrace_796180 : CollatzResearch.WordTrace tailWord_796180 prefixEnd_796180 408823027496800175788441 := by
  unfold tailWord_796180
  simp only [CollatzResearch.WordTrace]
  refine ⟨14519535127791655781724997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19359380170388874375633329 14519535127791655781724997)
  ·
    refine ⟨2722412836460935459073437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14519535127791655781724997 2722412836460935459073437)
    ·
      refine ⟨1020904813672850797152539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2722412836460935459073437 1020904813672850797152539)
      ·
        refine ⟨1531357220509276195728809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1020904813672850797152539 1531357220509276195728809)
        ·
          refine ⟨1148517915381957146796607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1531357220509276195728809 1148517915381957146796607)
          ·
            refine ⟨1722776873072935720194911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1148517915381957146796607 1722776873072935720194911)
            ·
              refine ⟨2584165309609403580292367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1722776873072935720194911 2584165309609403580292367)
              ·
                refine ⟨3876247964414105370438551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2584165309609403580292367 3876247964414105370438551)
                ·
                  refine ⟨5814371946621158055657827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3876247964414105370438551 5814371946621158055657827)
                  ·
                    refine ⟨8721557919931737083486741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5814371946621158055657827 8721557919931737083486741)
                    ·
                      refine ⟨408823027496800175788441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8721557919931737083486741 408823027496800175788441)
                      ·
                        rfl

theorem cell23_796180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_796180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_796180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_796180 prefixEnd_796180 := by exact prefixLift 796180
  have htrace : WordTrace (prefixWord ++ tailWord_796180) baseStart_796180 baseEnd_796180 := by
    simpa [prefixWord, tailWord_796180, baseEnd_796180] using wordTrace_append hprefix tailTrace_796180
  have hstable : (prefixWord ++ tailWord_796180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796180).length < 2 ^ (prefixWord ++ tailWord_796180).sum := by decide
  have hdescent : baseEnd_796180 < baseStart_796180 := by decide
  rcases family_descends (prefixWord ++ tailWord_796180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796274 : List Nat := [3, 2, 1, 2, 3, 2, 2, 2, 2, 2, 2]
def baseStart_796274 : Nat := 118140960795 + 796274 * 2 ^ 59
def prefixEnd_796274 : Nat := 4983230072969 + 3 ^ 40 * 796274 * 2
def baseEnd_796274 : Nat := 408871294678322808013009

theorem tailTrace_796274 : CollatzResearch.WordTrace tailWord_796274 prefixEnd_796274 408871294678322808013009 := by
  unfold tailWord_796274
  simp only [CollatzResearch.WordTrace]
  refine ⟨7260624679310691404342969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19361665811495177078247917 7260624679310691404342969)
  ·
    refine ⟨5445468509483018553257227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7260624679310691404342969 5445468509483018553257227)
    ·
      refine ⟨8168202764224527829885841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5445468509483018553257227 8168202764224527829885841)
      ·
        refine ⟨6126152073168395872414381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8168202764224527829885841 6126152073168395872414381)
        ·
          refine ⟨2297307027438148452155393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6126152073168395872414381 2297307027438148452155393)
          ·
            refine ⟨1722980270578611339116545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2297307027438148452155393 1722980270578611339116545)
            ·
              refine ⟨1292235202933958504337409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1722980270578611339116545 1292235202933958504337409)
              ·
                refine ⟨969176402200468878253057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1292235202933958504337409 969176402200468878253057)
                ·
                  refine ⟨726882301650351658689793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 969176402200468878253057 726882301650351658689793)
                  ·
                    refine ⟨545161726237763744017345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 726882301650351658689793 545161726237763744017345)
                    ·
                      refine ⟨408871294678322808013009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 545161726237763744017345 408871294678322808013009)
                      ·
                        rfl

theorem cell23_796274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 2, 2, 2, 2].length) (baseStart_796274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_796274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_796274 prefixEnd_796274 := by exact prefixLift 796274
  have htrace : WordTrace (prefixWord ++ tailWord_796274) baseStart_796274 baseEnd_796274 := by
    simpa [prefixWord, tailWord_796274, baseEnd_796274] using wordTrace_append hprefix tailTrace_796274
  have hstable : (prefixWord ++ tailWord_796274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796274).length < 2 ^ (prefixWord ++ tailWord_796274).sum := by decide
  have hdescent : baseEnd_796274 < baseStart_796274 := by decide
  rcases family_descends (prefixWord ++ tailWord_796274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796283 : List Nat := [1, 1, 1, 1, 1, 4, 3, 1, 1, 7, 2]
def baseStart_796283 : Nat := 118140960795 + 796283 * 2 ^ 59
def prefixEnd_796283 : Nat := 4983230072969 + 3 ^ 40 * 796283 * 2
def baseEnd_796283 : Nat := 408875916004213272800467

theorem tailTrace_796283 : CollatzResearch.WordTrace tailWord_796283 prefixEnd_796283 408875916004213272800467 := by
  unfold tailWord_796283
  simp only [CollatzResearch.WordTrace]
  refine ⟨29042826974210160154449503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19361884649473440102966335 29042826974210160154449503)
  ·
    refine ⟨43564240461315240231674255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29042826974210160154449503 43564240461315240231674255)
    ·
      refine ⟨65346360691972860347511383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43564240461315240231674255 65346360691972860347511383)
      ·
        refine ⟨98019541037959290521267075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65346360691972860347511383 98019541037959290521267075)
        ·
          refine ⟨147029311556938935781900613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98019541037959290521267075 147029311556938935781900613)
          ·
            refine ⟨27567995916926050459106365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 147029311556938935781900613 27567995916926050459106365)
            ·
              refine ⟨10337998468847268922164887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27567995916926050459106365 10337998468847268922164887)
              ·
                refine ⟨15506997703270903383247331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10337998468847268922164887 15506997703270903383247331)
                ·
                  refine ⟨23260496554906355074870997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15506997703270903383247331 23260496554906355074870997)
                  ·
                    refine ⟨545167888005617697067289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23260496554906355074870997 545167888005617697067289)
                    ·
                      refine ⟨408875916004213272800467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 545167888005617697067289 408875916004213272800467)
                      ·
                        rfl

theorem cell23_796283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 7, 2].length) (baseStart_796283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_796283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_796283 prefixEnd_796283 := by exact prefixLift 796283
  have htrace : WordTrace (prefixWord ++ tailWord_796283) baseStart_796283 baseEnd_796283 := by
    simpa [prefixWord, tailWord_796283, baseEnd_796283] using wordTrace_append hprefix tailTrace_796283
  have hstable : (prefixWord ++ tailWord_796283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796283).length < 2 ^ (prefixWord ++ tailWord_796283).sum := by decide
  have hdescent : baseEnd_796283 < baseStart_796283 := by decide
  rcases family_descends (prefixWord ++ tailWord_796283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796313 : List Nat := [1, 2, 1, 2, 1, 2, 2, 5, 2, 1, 4]
def baseStart_796313 : Nat := 118140960795 + 796313 * 2 ^ 59
def prefixEnd_796313 : Nat := 4983230072969 + 3 ^ 40 * 796313 * 2
def baseEnd_796313 : Nat := 408891320423848155425329

theorem tailTrace_796313 : CollatzResearch.WordTrace tailWord_796313 prefixEnd_796313 408891320423848155425329 := by
  unfold tailWord_796313
  simp only [CollatzResearch.WordTrace]
  refine ⟨29043921164101475278041593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19362614109400983518694395 29043921164101475278041593)
  ·
    refine ⟨21782940873076106458531195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29043921164101475278041593 21782940873076106458531195)
    ·
      refine ⟨32674411309614159687796793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21782940873076106458531195 32674411309614159687796793)
      ·
        refine ⟨24505808482210619765847595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32674411309614159687796793 24505808482210619765847595)
        ·
          refine ⟨36758712723315929648771393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24505808482210619765847595 36758712723315929648771393)
          ·
            refine ⟨27569034542486947236578545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36758712723315929648771393 27569034542486947236578545)
            ·
              refine ⟨20676775906865210427433909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27569034542486947236578545 20676775906865210427433909)
              ·
                refine ⟨1938447741268613477571929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20676775906865210427433909 1938447741268613477571929)
                ·
                  refine ⟨1453835805951460108178947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1938447741268613477571929 1453835805951460108178947)
                  ·
                    refine ⟨2180753708927190162268421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1453835805951460108178947 2180753708927190162268421)
                    ·
                      refine ⟨408891320423848155425329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2180753708927190162268421 408891320423848155425329)
                      ·
                        rfl

theorem cell23_796313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 5, 2, 1, 4].length) (baseStart_796313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_796313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_796313 prefixEnd_796313 := by exact prefixLift 796313
  have htrace : WordTrace (prefixWord ++ tailWord_796313) baseStart_796313 baseEnd_796313 := by
    simpa [prefixWord, tailWord_796313, baseEnd_796313] using wordTrace_append hprefix tailTrace_796313
  have hstable : (prefixWord ++ tailWord_796313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796313).length < 2 ^ (prefixWord ++ tailWord_796313).sum := by decide
  have hdescent : baseEnd_796313 < baseStart_796313 := by decide
  rcases family_descends (prefixWord ++ tailWord_796313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796323 : List Nat := [1, 1, 1, 4, 1, 1, 3, 2, 5, 4]
def baseStart_796323 : Nat := 118140960795 + 796323 * 2 ^ 59
def prefixEnd_796323 : Nat := 4983230072969 + 3 ^ 40 * 796323 * 2
def baseEnd_796323 : Nat := 136298818410131038766761

theorem tailTrace_796323 : CollatzResearch.WordTrace tailWord_796323 prefixEnd_796323 136298818410131038766761 := by
  unfold tailWord_796323
  simp only [CollatzResearch.WordTrace]
  refine ⟨29044285894065246985905623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19362857262710164657270415 29044285894065246985905623)
  ·
    refine ⟨43566428841097870478858435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29044285894065246985905623 43566428841097870478858435)
    ·
      refine ⟨65349643261646805718287653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43566428841097870478858435 65349643261646805718287653)
      ·
        refine ⟨12253058111558776072178935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65349643261646805718287653 12253058111558776072178935)
        ·
          refine ⟨18379587167338164108268403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12253058111558776072178935 18379587167338164108268403)
          ·
            refine ⟨27569380751007246162402605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18379587167338164108268403 27569380751007246162402605)
            ·
              refine ⟨10338517781627717310900977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27569380751007246162402605 10338517781627717310900977)
              ·
                refine ⟨7753888336220787983175733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10338517781627717310900977 7753888336220787983175733)
                ·
                  refine ⟨726927031520698873422725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7753888336220787983175733 726927031520698873422725)
                  ·
                    refine ⟨136298818410131038766761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 726927031520698873422725 136298818410131038766761)
                    ·
                      rfl

theorem cell23_796323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 5, 4].length) (baseStart_796323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_796323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_796323 prefixEnd_796323 := by exact prefixLift 796323
  have htrace : WordTrace (prefixWord ++ tailWord_796323) baseStart_796323 baseEnd_796323 := by
    simpa [prefixWord, tailWord_796323, baseEnd_796323] using wordTrace_append hprefix tailTrace_796323
  have hstable : (prefixWord ++ tailWord_796323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796323).length < 2 ^ (prefixWord ++ tailWord_796323).sum := by decide
  have hdescent : baseEnd_796323 < baseStart_796323 := by decide
  rcases family_descends (prefixWord ++ tailWord_796323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796350 : List Nat := [4, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3]
def baseStart_796350 : Nat := 118140960795 + 796350 * 2 ^ 59
def prefixEnd_796350 : Nat := 4983230072969 + 3 ^ 40 * 796350 * 2
def baseEnd_796350 : Nat := 408910319208064510662659

theorem tailTrace_796350 : CollatzResearch.WordTrace tailWord_796350 prefixEnd_796350 408910319208064510662659 := by
  unfold tailWord_796350
  simp only [CollatzResearch.WordTrace]
  refine ⟨3630658833120928824642313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19363513776644953731425669 3630658833120928824642313)
  ·
    refine ⟨2722994124840696618481735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3630658833120928824642313 2722994124840696618481735)
    ·
      refine ⟨4084491187261044927722603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2722994124840696618481735 4084491187261044927722603)
      ·
        refine ⟨6126736780891567391583905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4084491187261044927722603 6126736780891567391583905)
        ·
          refine ⟨4595052585668675543687929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6126736780891567391583905 4595052585668675543687929)
          ·
            refine ⟨3446289439251506657765947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4595052585668675543687929 3446289439251506657765947)
            ·
              refine ⟨5169434158877259986648921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3446289439251506657765947 5169434158877259986648921)
              ·
                refine ⟨3877075619157944989986691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5169434158877259986648921 3877075619157944989986691)
                ·
                  refine ⟨5815613428736917484980037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3877075619157944989986691 5815613428736917484980037)
                  ·
                    refine ⟨1090427517888172028433757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5815613428736917484980037 1090427517888172028433757)
                    ·
                      refine ⟨408910319208064510662659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1090427517888172028433757 408910319208064510662659)
                      ·
                        rfl

theorem cell23_796350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_796350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_796350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_796350 prefixEnd_796350 := by exact prefixLift 796350
  have htrace : WordTrace (prefixWord ++ tailWord_796350) baseStart_796350 baseEnd_796350 := by
    simpa [prefixWord, tailWord_796350, baseEnd_796350] using wordTrace_append hprefix tailTrace_796350
  have hstable : (prefixWord ++ tailWord_796350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796350).length < 2 ^ (prefixWord ++ tailWord_796350).sum := by decide
  have hdescent : baseEnd_796350 < baseStart_796350 := by decide
  rcases family_descends (prefixWord ++ tailWord_796350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796391 : List Nat := [1, 1, 5, 4, 2, 1, 1, 1, 3, 4]
def baseStart_796391 : Nat := 118140960795 + 796391 * 2 ^ 59
def prefixEnd_796391 : Nat := 4983230072969 + 3 ^ 40 * 796391 * 2
def baseEnd_796391 : Nat := 136310457304966283416657

theorem tailTrace_796391 : CollatzResearch.WordTrace tailWord_796391 prefixEnd_796391 136310457304966283416657 := by
  unfold tailWord_796391
  simp only [CollatzResearch.WordTrace]
  refine ⟨29046766057818894599381027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19364510705212596399587351 29046766057818894599381027)
  ·
    refine ⟨43570149086728341899071541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29046766057818894599381027 43570149086728341899071541)
    ·
      refine ⟨4084701476880782053037957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43570149086728341899071541 4084701476880782053037957)
      ·
        refine ⟨765881526915146634944617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4084701476880782053037957 765881526915146634944617)
        ·
          refine ⟨574411145186359976208463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 765881526915146634944617 574411145186359976208463)
          ·
            refine ⟨861616717779539964312695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 574411145186359976208463 861616717779539964312695)
            ·
              refine ⟨1292425076669309946469043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 861616717779539964312695 1292425076669309946469043)
              ·
                refine ⟨1938637615003964919703565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1292425076669309946469043 1938637615003964919703565)
                ·
                  refine ⟨726989105626486844888837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1938637615003964919703565 726989105626486844888837)
                  ·
                    refine ⟨136310457304966283416657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 726989105626486844888837 136310457304966283416657)
                    ·
                      rfl

theorem cell23_796391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 1, 3, 4].length) (baseStart_796391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_796391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_796391 prefixEnd_796391 := by exact prefixLift 796391
  have htrace : WordTrace (prefixWord ++ tailWord_796391) baseStart_796391 baseEnd_796391 := by
    simpa [prefixWord, tailWord_796391, baseEnd_796391] using wordTrace_append hprefix tailTrace_796391
  have hstable : (prefixWord ++ tailWord_796391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796391).length < 2 ^ (prefixWord ++ tailWord_796391).sum := by decide
  have hdescent : baseEnd_796391 < baseStart_796391 := by decide
  rcases family_descends (prefixWord ++ tailWord_796391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796404 : List Nat := [2, 6, 1, 1, 1, 2, 1, 3, 6]
def baseStart_796404 : Nat := 118140960795 + 796404 * 2 ^ 59
def prefixEnd_796404 : Nat := 4983230072969 + 3 ^ 40 * 796404 * 2
def baseEnd_796404 : Nat := 45437560795934144376379

theorem tailTrace_796404 : CollatzResearch.WordTrace tailWord_796404 prefixEnd_796404 45437560795934144376379 := by
  unfold tailWord_796404
  simp only [CollatzResearch.WordTrace]
  refine ⟨14523620103385898909802133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19364826804514531879736177 14523620103385898909802133)
  ·
    refine ⟨680794692346214011396975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14523620103385898909802133 680794692346214011396975)
    ·
      refine ⟨1021192038519321017095463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 680794692346214011396975 1021192038519321017095463)
      ·
        refine ⟨1531788057778981525643195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1021192038519321017095463 1531788057778981525643195)
        ·
          refine ⟨2297682086668472288464793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1531788057778981525643195 2297682086668472288464793)
          ·
            refine ⟨1723261565001354216348595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2297682086668472288464793 1723261565001354216348595)
            ·
              refine ⟨2584892347502031324522893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1723261565001354216348595 2584892347502031324522893)
              ·
                refine ⟨969334630313261746696085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2584892347502031324522893 969334630313261746696085)
                ·
                  refine ⟨45437560795934144376379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 969334630313261746696085 45437560795934144376379)
                  ·
                    rfl

theorem cell23_796404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_796404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_796404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_796404 prefixEnd_796404 := by exact prefixLift 796404
  have htrace : WordTrace (prefixWord ++ tailWord_796404) baseStart_796404 baseEnd_796404 := by
    simpa [prefixWord, tailWord_796404, baseEnd_796404] using wordTrace_append hprefix tailTrace_796404
  have hstable : (prefixWord ++ tailWord_796404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796404).length < 2 ^ (prefixWord ++ tailWord_796404).sum := by decide
  have hdescent : baseEnd_796404 < baseStart_796404 := by decide
  rcases family_descends (prefixWord ++ tailWord_796404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796430 : List Nat := [4, 1, 1, 2, 1, 1, 2, 1, 6, 4]
def baseStart_796430 : Nat := 118140960795 + 796430 * 2 ^ 59
def prefixEnd_796430 : Nat := 4983230072969 + 3 ^ 40 * 796430 * 2
def baseEnd_796430 : Nat := 136317132553474732554097

theorem tailTrace_796430 : CollatzResearch.WordTrace tailWord_796430 prefixEnd_796430 136317132553474732554097 := by
  unfold tailWord_796430
  simp only [CollatzResearch.WordTrace]
  refine ⟨3631023563084700532506343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19365459003118402840033829 3631023563084700532506343)
  ·
    refine ⟨5446535344627050798759515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3631023563084700532506343 5446535344627050798759515)
    ·
      refine ⟨8169803016940576198139273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5446535344627050798759515 8169803016940576198139273)
      ·
        refine ⟨6127352262705432148604455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8169803016940576198139273 6127352262705432148604455)
        ·
          refine ⟨9191028394058148222906683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6127352262705432148604455 9191028394058148222906683)
          ·
            refine ⟨13786542591087222334360025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9191028394058148222906683 13786542591087222334360025)
            ·
              refine ⟨10339906943315416750770019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13786542591087222334360025 10339906943315416750770019)
              ·
                refine ⟨15509860414973125126155029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10339906943315416750770019 15509860414973125126155029)
                ·
                  refine ⟨727024706951865240288517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 15509860414973125126155029 727024706951865240288517)
                  ·
                    refine ⟨136317132553474732554097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 727024706951865240288517 136317132553474732554097)
                    ·
                      rfl

theorem cell23_796430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 6, 4].length) (baseStart_796430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_796430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_796430 prefixEnd_796430 := by exact prefixLift 796430
  have htrace : WordTrace (prefixWord ++ tailWord_796430) baseStart_796430 baseEnd_796430 := by
    simpa [prefixWord, tailWord_796430, baseEnd_796430] using wordTrace_append hprefix tailTrace_796430
  have hstable : (prefixWord ++ tailWord_796430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796430).length < 2 ^ (prefixWord ++ tailWord_796430).sum := by decide
  have hdescent : baseEnd_796430 < baseStart_796430 := by decide
  rcases family_descends (prefixWord ++ tailWord_796430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796440 : List Nat := [2, 1, 2, 3, 1, 1, 5, 1, 1, 1, 5]
def baseStart_796440 : Nat := 118140960795 + 796440 * 2 ^ 59
def prefixEnd_796440 : Nat := 4983230072969 + 3 ^ 40 * 796440 * 2
def baseEnd_796440 : Nat := 408956532466969158537245

theorem tailTrace_796440 : CollatzResearch.WordTrace tailWord_796440 prefixEnd_796440 408956532466969158537245 := by
  unfold tailWord_796440
  simp only [CollatzResearch.WordTrace]
  refine ⟨14524276617320687983957387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19365702156427583978609849 14524276617320687983957387)
  ·
    refine ⟨21786414925981031975936081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14524276617320687983957387 21786414925981031975936081)
    ·
      refine ⟨16339811194485773981952061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21786414925981031975936081 16339811194485773981952061)
      ·
        refine ⟨6127429197932165243232023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16339811194485773981952061 6127429197932165243232023)
        ·
          refine ⟨9191143796898247864848035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6127429197932165243232023 9191143796898247864848035)
          ·
            refine ⟨13786715695347371797272053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9191143796898247864848035 13786715695347371797272053)
            ·
              refine ⟨1292504596438816105994255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13786715695347371797272053 1292504596438816105994255)
              ·
                refine ⟨1938756894658224158991383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1292504596438816105994255 1938756894658224158991383)
                ·
                  refine ⟨2908135341987336238487075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1938756894658224158991383 2908135341987336238487075)
                  ·
                    refine ⟨4362203012981004357730613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2908135341987336238487075 4362203012981004357730613)
                    ·
                      refine ⟨408956532466969158537245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4362203012981004357730613 408956532466969158537245)
                      ·
                        rfl

theorem cell23_796440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_796440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_796440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_796440 prefixEnd_796440 := by exact prefixLift 796440
  have htrace : WordTrace (prefixWord ++ tailWord_796440) baseStart_796440 baseEnd_796440 := by
    simpa [prefixWord, tailWord_796440, baseEnd_796440] using wordTrace_append hprefix tailTrace_796440
  have hstable : (prefixWord ++ tailWord_796440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796440).length < 2 ^ (prefixWord ++ tailWord_796440).sum := by decide
  have hdescent : baseEnd_796440 < baseStart_796440 := by decide
  rcases family_descends (prefixWord ++ tailWord_796440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796447 : List Nat := [1, 1, 2, 4, 2, 1, 4, 2, 2, 4]
def baseStart_796447 : Nat := 118140960795 + 796447 * 2 ^ 59
def prefixEnd_796447 : Nat := 4983230072969 + 3 ^ 40 * 796447 * 2
def baseEnd_796447 : Nat := 136320042277183543716571

theorem tailTrace_796447 : CollatzResearch.WordTrace tailWord_796447 prefixEnd_796447 136320042277183543716571 := by
  unfold tailWord_796447
  simp only [CollatzResearch.WordTrace]
  refine ⟨29048808545616016163419595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19365872363744010775613063 29048808545616016163419595)
  ·
    refine ⟨43573212818424024245129393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29048808545616016163419595 43573212818424024245129393)
    ·
      refine ⟨32679909613818018183847045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43573212818424024245129393 32679909613818018183847045)
      ·
        refine ⟨6127483052590878409471321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32679909613818018183847045 6127483052590878409471321)
        ·
          refine ⟨4595612289443158807103491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6127483052590878409471321 4595612289443158807103491)
          ·
            refine ⟨6893418434164738210655237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4595612289443158807103491 6893418434164738210655237)
            ·
              refine ⟨1292515956405888414497857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6893418434164738210655237 1292515956405888414497857)
              ·
                refine ⟨969386967304416310873393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1292515956405888414497857 969386967304416310873393)
                ·
                  refine ⟨727040225478312233155045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 969386967304416310873393 727040225478312233155045)
                  ·
                    refine ⟨136320042277183543716571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 727040225478312233155045 136320042277183543716571)
                    ·
                      rfl

theorem cell23_796447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 2, 2, 4].length) (baseStart_796447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_796447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_796447 prefixEnd_796447 := by exact prefixLift 796447
  have htrace : WordTrace (prefixWord ++ tailWord_796447) baseStart_796447 baseEnd_796447 := by
    simpa [prefixWord, tailWord_796447, baseEnd_796447] using wordTrace_append hprefix tailTrace_796447
  have hstable : (prefixWord ++ tailWord_796447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796447).length < 2 ^ (prefixWord ++ tailWord_796447).sum := by decide
  have hdescent : baseEnd_796447 < baseStart_796447 := by decide
  rcases family_descends (prefixWord ++ tailWord_796447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796450 : List Nat := [3, 3, 1, 1, 2, 1, 1, 2, 3, 2, 4]
def baseStart_796450 : Nat := 118140960795 + 796450 * 2 ^ 59
def prefixEnd_796450 : Nat := 4983230072969 + 3 ^ 40 * 796450 * 2
def baseEnd_796450 : Nat := 408961667273514119412199

theorem tailTrace_796450 : CollatzResearch.WordTrace tailWord_796450 prefixEnd_796450 408961667273514119412199 := by
  unfold tailWord_796450
  simp only [CollatzResearch.WordTrace]
  refine ⟨7262229491151286918944701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19365945309736765117185869 7262229491151286918944701)
  ·
    refine ⟨2723336059181732594604263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7262229491151286918944701 2723336059181732594604263)
    ·
      refine ⟨4085004088772598891906395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2723336059181732594604263 4085004088772598891906395)
      ·
        refine ⟨6127506133158898337859593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4085004088772598891906395 6127506133158898337859593)
        ·
          refine ⟨4595629599869173753394695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6127506133158898337859593 4595629599869173753394695)
          ·
            refine ⟨6893444399803760630092043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4595629599869173753394695 6893444399803760630092043)
            ·
              refine ⟨10340166599705640945138065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6893444399803760630092043 10340166599705640945138065)
              ·
                refine ⟨7755124949779230708853549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10340166599705640945138065 7755124949779230708853549)
                ·
                  refine ⟨2908171856167211515820081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7755124949779230708853549 2908171856167211515820081)
                  ·
                    refine ⟨2181128892125408636865061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2908171856167211515820081 2181128892125408636865061)
                    ·
                      refine ⟨408961667273514119412199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2181128892125408636865061 408961667273514119412199)
                      ·
                        rfl

theorem cell23_796450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_796450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_796450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_796450 prefixEnd_796450 := by exact prefixLift 796450
  have htrace : WordTrace (prefixWord ++ tailWord_796450) baseStart_796450 baseEnd_796450 := by
    simpa [prefixWord, tailWord_796450, baseEnd_796450] using wordTrace_append hprefix tailTrace_796450
  have hstable : (prefixWord ++ tailWord_796450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796450).length < 2 ^ (prefixWord ++ tailWord_796450).sum := by decide
  have hdescent : baseEnd_796450 < baseStart_796450 := by decide
  rcases family_descends (prefixWord ++ tailWord_796450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796460 : List Nat := [2, 2, 1, 1, 1, 7, 1, 8]
def baseStart_796460 : Nat := 118140960795 + 796460 * 2 ^ 59
def prefixEnd_796460 : Nat := 4983230072969 + 3 ^ 40 * 796460 * 2
def baseEnd_796460 : Nat := 15146918595557743714339

theorem tailTrace_796460 : CollatzResearch.WordTrace tailWord_796460 prefixEnd_796460 15146918595557743714339 := by
  unfold tailWord_796460
  simp only [CollatzResearch.WordTrace]
  refine ⟨14524641347284459691821417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19366188463045946255761889 14524641347284459691821417)
  ·
    refine ⟨10893481010463344768866063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14524641347284459691821417 10893481010463344768866063)
    ·
      refine ⟨16340221515695017153299095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10893481010463344768866063 16340221515695017153299095)
      ·
        refine ⟨24510332273542525729948643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16340221515695017153299095 24510332273542525729948643)
        ·
          refine ⟨36765498410313788594922965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24510332273542525729948643 36765498410313788594922965)
          ·
            refine ⟨861691368991729420193507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 36765498410313788594922965 861691368991729420193507)
            ·
              refine ⟨1292537053487594130290261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 861691368991729420193507 1292537053487594130290261)
              ·
                refine ⟨15146918595557743714339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1292537053487594130290261 15146918595557743714339)
                ·
                  rfl

theorem cell23_796460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 8].length) (baseStart_796460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_796460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_796460 prefixEnd_796460 := by exact prefixLift 796460
  have htrace : WordTrace (prefixWord ++ tailWord_796460) baseStart_796460 baseEnd_796460 := by
    simpa [prefixWord, tailWord_796460, baseEnd_796460] using wordTrace_append hprefix tailTrace_796460
  have hstable : (prefixWord ++ tailWord_796460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796460).length < 2 ^ (prefixWord ++ tailWord_796460).sum := by decide
  have hdescent : baseEnd_796460 < baseStart_796460 := by decide
  rcases family_descends (prefixWord ++ tailWord_796460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796467 : List Nat := [1, 1, 1, 2, 7, 1, 2, 1, 1, 2, 4]
def baseStart_796467 : Nat := 118140960795 + 796467 * 2 ^ 59
def prefixEnd_796467 : Nat := 4983230072969 + 3 ^ 40 * 796467 * 2
def baseEnd_796467 : Nat := 408970396444640552899621

theorem tailTrace_796467 : CollatzResearch.WordTrace tailWord_796467 prefixEnd_796467 408970396444640552899621 := by
  unfold tailWord_796467
  simp only [CollatzResearch.WordTrace]
  refine ⟨29049538005543559579147655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19366358670362373052765103 29049538005543559579147655)
  ·
    refine ⟨43574307008315339368721483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29049538005543559579147655 43574307008315339368721483)
    ·
      refine ⟨65361460512473009053082225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43574307008315339368721483 65361460512473009053082225)
      ·
        refine ⟨49021095384354756789811669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65361460512473009053082225 49021095384354756789811669)
        ·
          refine ⟨1148931923070814612261211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 49021095384354756789811669 1148931923070814612261211)
          ·
            refine ⟨1723397884606221918391817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1148931923070814612261211 1723397884606221918391817)
            ·
              refine ⟨1292548413454666438793863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1723397884606221918391817 1292548413454666438793863)
              ·
                refine ⟨1938822620181999658190795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1292548413454666438793863 1938822620181999658190795)
                ·
                  refine ⟨2908233930272999487286193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1938822620181999658190795 2908233930272999487286193)
                  ·
                    refine ⟨2181175447704749615464645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2908233930272999487286193 2181175447704749615464645)
                    ·
                      refine ⟨408970396444640552899621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2181175447704749615464645 408970396444640552899621)
                      ·
                        rfl

theorem cell23_796467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 1, 1, 2, 4].length) (baseStart_796467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_796467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_796467 prefixEnd_796467 := by exact prefixLift 796467
  have htrace : WordTrace (prefixWord ++ tailWord_796467) baseStart_796467 baseEnd_796467 := by
    simpa [prefixWord, tailWord_796467, baseEnd_796467] using wordTrace_append hprefix tailTrace_796467
  have hstable : (prefixWord ++ tailWord_796467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796467).length < 2 ^ (prefixWord ++ tailWord_796467).sum := by decide
  have hdescent : baseEnd_796467 < baseStart_796467 := by decide
  rcases family_descends (prefixWord ++ tailWord_796467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796477 : List Nat := [1, 4, 1, 4, 1, 2, 3, 7]
def baseStart_796477 : Nat := 118140960795 + 796477 * 2 ^ 59
def prefixEnd_796477 : Nat := 4983230072969 + 3 ^ 40 * 796477 * 2
def baseEnd_796477 : Nat := 15147241898192056065725

theorem tailTrace_796477 : CollatzResearch.WordTrace tailWord_796477 prefixEnd_796477 15147241898192056065725 := by
  unfold tailWord_796477
  simp only [CollatzResearch.WordTrace]
  refine ⟨29049902735507331287011685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19366601823671554191341123 29049902735507331287011685)
  ·
    refine ⟨5446856762907624616314691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29049902735507331287011685 5446856762907624616314691)
    ·
      refine ⟨8170285144361436924472037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5446856762907624616314691 8170285144361436924472037)
      ·
        refine ⟨1531928464567769423338507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8170285144361436924472037 1531928464567769423338507)
        ·
          refine ⟨2297892696851654135007761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1531928464567769423338507 2297892696851654135007761)
          ·
            refine ⟨1723419522638740601255821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2297892696851654135007761 1723419522638740601255821)
            ·
              refine ⟨646282320989527725470933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1723419522638740601255821 646282320989527725470933)
              ·
                refine ⟨15147241898192056065725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 646282320989527725470933 15147241898192056065725)
                ·
                  rfl

theorem cell23_796477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 3, 7].length) (baseStart_796477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_796477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_796477 prefixEnd_796477 := by exact prefixLift 796477
  have htrace : WordTrace (prefixWord ++ tailWord_796477) baseStart_796477 baseEnd_796477 := by
    simpa [prefixWord, tailWord_796477, baseEnd_796477] using wordTrace_append hprefix tailTrace_796477
  have hstable : (prefixWord ++ tailWord_796477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796477).length < 2 ^ (prefixWord ++ tailWord_796477).sum := by decide
  have hdescent : baseEnd_796477 < baseStart_796477 := by decide
  rcases family_descends (prefixWord ++ tailWord_796477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796520 : List Nat := [2, 1, 4, 2, 1, 1, 1, 3, 2, 6]
def baseStart_796520 : Nat := 118140960795 + 796520 * 2 ^ 59
def prefixEnd_796520 : Nat := 4983230072969 + 3 ^ 40 * 796520 * 2
def baseEnd_796520 : Nat := 136332536973109615178959

theorem tailTrace_796520 : CollatzResearch.WordTrace tailWord_796520 prefixEnd_796520 136332536973109615178959 := by
  unfold tailWord_796520
  simp only [CollatzResearch.WordTrace]
  refine ⟨14525735537175774815413507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19367647382901033087218009 14525735537175774815413507)
  ·
    refine ⟨21788603305763662223120261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14525735537175774815413507 21788603305763662223120261)
    ·
      refine ⟨4085363119830686666835049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21788603305763662223120261 4085363119830686666835049)
      ·
        refine ⟨3064022339873015000126287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4085363119830686666835049 3064022339873015000126287)
        ·
          refine ⟨4596033509809522500189431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3064022339873015000126287 4596033509809522500189431)
          ·
            refine ⟨6894050264714283750284147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4596033509809522500189431 6894050264714283750284147)
            ·
              refine ⟨10341075397071425625426221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6894050264714283750284147 10341075397071425625426221)
              ·
                refine ⟨3877903273901784609534833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10341075397071425625426221 3877903273901784609534833)
                ·
                  refine ⟨2908427455426338457151125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3877903273901784609534833 2908427455426338457151125)
                  ·
                    refine ⟨136332536973109615178959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2908427455426338457151125 136332536973109615178959)
                    ·
                      rfl

theorem cell23_796520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_796520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_796520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_796520 prefixEnd_796520 := by exact prefixLift 796520
  have htrace : WordTrace (prefixWord ++ tailWord_796520) baseStart_796520 baseEnd_796520 := by
    simpa [prefixWord, tailWord_796520, baseEnd_796520] using wordTrace_append hprefix tailTrace_796520
  have hstable : (prefixWord ++ tailWord_796520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796520).length < 2 ^ (prefixWord ++ tailWord_796520).sum := by decide
  have hdescent : baseEnd_796520 < baseStart_796520 := by decide
  rcases family_descends (prefixWord ++ tailWord_796520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796530 : List Nat := [3, 2, 1, 2, 1, 1, 1, 4, 2, 1, 5]
def baseStart_796530 : Nat := 118140960795 + 796530 * 2 ^ 59
def prefixEnd_796530 : Nat := 4983230072969 + 3 ^ 40 * 796530 * 2
def baseEnd_796530 : Nat := 409002745725873806411831

theorem tailTrace_796530 : CollatzResearch.WordTrace tailWord_796530 prefixEnd_796530 409002745725873806411831 := by
  unfold tailWord_796530
  simp only [CollatzResearch.WordTrace]
  refine ⟨7262958951078830334672761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19367890536210214225794029 7262958951078830334672761)
  ·
    refine ⟨5447219213309122751004571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7262958951078830334672761 5447219213309122751004571)
    ·
      refine ⟨8170828819963684126506857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5447219213309122751004571 8170828819963684126506857)
      ·
        refine ⟨6128121614972763094880143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8170828819963684126506857 6128121614972763094880143)
        ·
          refine ⟨9192182422459144642320215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6128121614972763094880143 9192182422459144642320215)
          ·
            refine ⟨13788273633688716963480323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9192182422459144642320215 13788273633688716963480323)
            ·
              refine ⟨20682410450533075445220485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13788273633688716963480323 20682410450533075445220485)
              ·
                refine ⟨3877951959474951645978841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20682410450533075445220485 3877951959474951645978841)
                ·
                  refine ⟨2908463969606213734484131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3877951959474951645978841 2908463969606213734484131)
                  ·
                    refine ⟨4362695954409320601726197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2908463969606213734484131 4362695954409320601726197)
                    ·
                      refine ⟨409002745725873806411831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4362695954409320601726197 409002745725873806411831)
                      ·
                        rfl

theorem cell23_796530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_796530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_796530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_796530 prefixEnd_796530 := by exact prefixLift 796530
  have htrace : WordTrace (prefixWord ++ tailWord_796530) baseStart_796530 baseEnd_796530 := by
    simpa [prefixWord, tailWord_796530, baseEnd_796530] using wordTrace_append hprefix tailTrace_796530
  have hstable : (prefixWord ++ tailWord_796530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796530).length < 2 ^ (prefixWord ++ tailWord_796530).sum := by decide
  have hdescent : baseEnd_796530 < baseStart_796530 := by decide
  rcases family_descends (prefixWord ++ tailWord_796530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796567 : List Nat := [1, 1, 3, 3, 1, 5, 1, 1, 7]
def baseStart_796567 : Nat := 118140960795 + 796567 * 2 ^ 59
def prefixEnd_796567 : Nat := 4983230072969 + 3 ^ 40 * 796567 * 2
def baseEnd_796567 : Nat := 45446860501121129072129

theorem tailTrace_796567 : CollatzResearch.WordTrace tailWord_796567 prefixEnd_796567 45446860501121129072129 := by
  unfold tailWord_796567
  simp only [CollatzResearch.WordTrace]
  refine ⟨29053185305181276657787955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19368790203454184438525303 29053185305181276657787955)
  ·
    refine ⟨43579777957771914986681933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29053185305181276657787955 43579777957771914986681933)
    ·
      refine ⟨16342416734164468120005725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43579777957771914986681933 16342416734164468120005725)
      ·
        refine ⟨6128406275311675545002147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16342416734164468120005725 6128406275311675545002147)
        ·
          refine ⟨9192609412967513317503221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6128406275311675545002147 9192609412967513317503221)
          ·
            refine ⟨861807132465704373515927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9192609412967513317503221 861807132465704373515927)
            ·
              refine ⟨1292710698698556560273891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 861807132465704373515927 1292710698698556560273891)
              ·
                refine ⟨1939066048047834840410837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1292710698698556560273891 1939066048047834840410837)
                ·
                  refine ⟨45446860501121129072129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1939066048047834840410837 45446860501121129072129)
                  ·
                    rfl

theorem cell23_796567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 1, 7].length) (baseStart_796567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_796567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_796567 prefixEnd_796567 := by exact prefixLift 796567
  have htrace : WordTrace (prefixWord ++ tailWord_796567) baseStart_796567 baseEnd_796567 := by
    simpa [prefixWord, tailWord_796567, baseEnd_796567] using wordTrace_append hprefix tailTrace_796567
  have hstable : (prefixWord ++ tailWord_796567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796567).length < 2 ^ (prefixWord ++ tailWord_796567).sum := by decide
  have hdescent : baseEnd_796567 < baseStart_796567 := by decide
  rcases family_descends (prefixWord ++ tailWord_796567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796578 : List Nat := [3, 3, 1, 2, 3, 1, 1, 3, 2, 2, 2]
def baseStart_796578 : Nat := 118140960795 + 796578 * 2 ^ 59
def prefixEnd_796578 : Nat := 4983230072969 + 3 ^ 40 * 796578 * 2
def baseEnd_796578 : Nat := 409027392797289618611611

theorem tailTrace_796578 : CollatzResearch.WordTrace tailWord_796578 prefixEnd_796578 409027392797289618611611 := by
  unfold tailWord_796578
  simp only [CollatzResearch.WordTrace]
  refine ⟨7263396627035356384109597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19369057672094283690958925 7263396627035356384109597)
  ·
    refine ⟨2723773735138258644041099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7263396627035356384109597 2723773735138258644041099)
    ·
      refine ⟨4085660602707387966061649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2723773735138258644041099 4085660602707387966061649)
      ·
        refine ⟨3064245452030540974546237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4085660602707387966061649 3064245452030540974546237)
        ·
          refine ⟨1149092044511452865454839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3064245452030540974546237 1149092044511452865454839)
          ·
            refine ⟨1723638066767179298182259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1149092044511452865454839 1723638066767179298182259)
            ·
              refine ⟨2585457100150768947273389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1723638066767179298182259 2585457100150768947273389)
              ·
                refine ⟨969546412556538355227521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2585457100150768947273389 969546412556538355227521)
                ·
                  refine ⟨727159809417403766420641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 969546412556538355227521 727159809417403766420641)
                  ·
                    refine ⟨545369857063052824815481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 727159809417403766420641 545369857063052824815481)
                    ·
                      refine ⟨409027392797289618611611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 545369857063052824815481 409027392797289618611611)
                      ·
                        rfl

theorem cell23_796578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_796578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_796578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_796578 prefixEnd_796578 := by exact prefixLift 796578
  have htrace : WordTrace (prefixWord ++ tailWord_796578) baseStart_796578 baseEnd_796578 := by
    simpa [prefixWord, tailWord_796578, baseEnd_796578] using wordTrace_append hprefix tailTrace_796578
  have hstable : (prefixWord ++ tailWord_796578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796578).length < 2 ^ (prefixWord ++ tailWord_796578).sum := by decide
  have hdescent : baseEnd_796578 < baseStart_796578 := by decide
  rcases family_descends (prefixWord ++ tailWord_796578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796597 : List Nat := [1, 3, 3, 2, 1, 2, 1, 3, 2, 5]
def baseStart_796597 : Nat := 118140960795 + 796597 * 2 ^ 59
def prefixEnd_796597 : Nat := 4983230072969 + 3 ^ 40 * 796597 * 2
def baseEnd_796597 : Nat := 136345716309908348091341

theorem tailTrace_796597 : CollatzResearch.WordTrace tailWord_796597 prefixEnd_796597 136345716309908348091341 := by
  unfold tailWord_796597
  simp only [CollatzResearch.WordTrace]
  refine ⟨29054279495072591781380045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19369519663381727854253363 29054279495072591781380045)
  ·
    refine ⟨10895354810652221918017517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29054279495072591781380045 10895354810652221918017517)
    ·
      refine ⟨4085758053994583219256569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10895354810652221918017517 4085758053994583219256569)
      ·
        refine ⟨3064318540495937414442427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4085758053994583219256569 3064318540495937414442427)
        ·
          refine ⟨4596477810743906121663641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3064318540495937414442427 4596477810743906121663641)
          ·
            refine ⟨3447358358057929591247731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4596477810743906121663641 3447358358057929591247731)
            ·
              refine ⟨5171037537086894386871597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3447358358057929591247731 5171037537086894386871597)
              ·
                refine ⟨1939139076407585395076849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5171037537086894386871597 1939139076407585395076849)
                ·
                  refine ⟨1454354307305689046307637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1939139076407585395076849 1454354307305689046307637)
                  ·
                    refine ⟨136345716309908348091341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1454354307305689046307637 136345716309908348091341)
                    ·
                      rfl

theorem cell23_796597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_796597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_796597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_796597 prefixEnd_796597 := by exact prefixLift 796597
  have htrace : WordTrace (prefixWord ++ tailWord_796597) baseStart_796597 baseEnd_796597 := by
    simpa [prefixWord, tailWord_796597, baseEnd_796597] using wordTrace_append hprefix tailTrace_796597
  have hstable : (prefixWord ++ tailWord_796597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796597).length < 2 ^ (prefixWord ++ tailWord_796597).sum := by decide
  have hdescent : baseEnd_796597 < baseStart_796597 := by decide
  rcases family_descends (prefixWord ++ tailWord_796597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796617 : List Nat := [1, 2, 1, 1, 2, 1, 2, 3, 4, 4, 2]
def baseStart_796617 : Nat := 118140960795 + 796617 * 2 ^ 59
def prefixEnd_796617 : Nat := 4983230072969 + 3 ^ 40 * 796617 * 2
def baseEnd_796617 : Nat := 409047418542814966023931

theorem tailTrace_796617 : CollatzResearch.WordTrace tailWord_796617 prefixEnd_796617 409047418542814966023931 := by
  unfold tailWord_796617
  simp only [CollatzResearch.WordTrace]
  refine ⟨29055008955000135197108105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19370005970000090131405403 29055008955000135197108105)
  ·
    refine ⟨21791256716250101397831079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29055008955000135197108105 21791256716250101397831079)
    ·
      refine ⟨32686885074375152096746619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21791256716250101397831079 32686885074375152096746619)
      ·
        refine ⟨49030327611562728145119929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32686885074375152096746619 49030327611562728145119929)
        ·
          refine ⟨36772745708672046108839947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49030327611562728145119929 36772745708672046108839947)
          ·
            refine ⟨55159118563008069163259921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36772745708672046108839947 55159118563008069163259921)
            ·
              refine ⟨41369338922256051872444941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55159118563008069163259921 41369338922256051872444941)
              ·
                refine ⟨15513502095846019452166853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41369338922256051872444941 15513502095846019452166853)
                ·
                  refine ⟨2908781642971128647281285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15513502095846019452166853 2908781642971128647281285)
                  ·
                    refine ⟨545396558057086621365241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2908781642971128647281285 545396558057086621365241)
                    ·
                      refine ⟨409047418542814966023931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 545396558057086621365241 409047418542814966023931)
                      ·
                        rfl

theorem cell23_796617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 4, 4, 2].length) (baseStart_796617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_796617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_796617 prefixEnd_796617 := by exact prefixLift 796617
  have htrace : WordTrace (prefixWord ++ tailWord_796617) baseStart_796617 baseEnd_796617 := by
    simpa [prefixWord, tailWord_796617, baseEnd_796617] using wordTrace_append hprefix tailTrace_796617
  have hstable : (prefixWord ++ tailWord_796617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796617).length < 2 ^ (prefixWord ++ tailWord_796617).sum := by decide
  have hdescent : baseEnd_796617 < baseStart_796617 := by decide
  rcases family_descends (prefixWord ++ tailWord_796617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796654 : List Nat := [4, 1, 2, 1, 3, 2, 1, 1, 1, 4, 3]
def baseStart_796654 : Nat := 118140960795 + 796654 * 2 ^ 59
def prefixEnd_796654 : Nat := 4983230072969 + 3 ^ 40 * 796654 * 2
def baseEnd_796654 : Nat := 409066417327031321261261

theorem tailTrace_796654 : CollatzResearch.WordTrace tailWord_796654 prefixEnd_796654 409066417327031321261261 := by
  unfold tailWord_796654
  simp only [CollatzResearch.WordTrace]
  refine ⟨3632044806983261314525627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19370905637244060344136677 3632044806983261314525627)
  ·
    refine ⟨5448067210474891971788441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3632044806983261314525627 5448067210474891971788441)
    ·
      refine ⟨4086050407856168978841331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5448067210474891971788441 4086050407856168978841331)
      ·
        refine ⟨6129075611784253468261997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4086050407856168978841331 6129075611784253468261997)
        ·
          refine ⟨2298403354419095050598249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6129075611784253468261997 2298403354419095050598249)
          ·
            refine ⟨1723802515814321287948687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2298403354419095050598249 1723802515814321287948687)
            ·
              refine ⟨2585703773721481931923031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1723802515814321287948687 2585703773721481931923031)
              ·
                refine ⟨3878555660582222897884547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2585703773721481931923031 3878555660582222897884547)
                ·
                  refine ⟨5817833490873334346826821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3878555660582222897884547 5817833490873334346826821)
                  ·
                    refine ⟨1090843779538750190030029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5817833490873334346826821 1090843779538750190030029)
                    ·
                      refine ⟨409066417327031321261261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1090843779538750190030029 409066417327031321261261)
                      ·
                        rfl

theorem cell23_796654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_796654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_796654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_796654 prefixEnd_796654 := by exact prefixLift 796654
  have htrace : WordTrace (prefixWord ++ tailWord_796654) baseStart_796654 baseEnd_796654 := by
    simpa [prefixWord, tailWord_796654, baseEnd_796654] using wordTrace_append hprefix tailTrace_796654
  have hstable : (prefixWord ++ tailWord_796654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796654).length < 2 ^ (prefixWord ++ tailWord_796654).sum := by decide
  have hdescent : baseEnd_796654 < baseStart_796654 := by decide
  rcases family_descends (prefixWord ++ tailWord_796654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796701 : List Nat := [1, 4, 2, 2, 2, 1, 2, 2, 3, 1, 3]
def baseStart_796701 : Nat := 118140960795 + 796701 * 2 ^ 59
def prefixEnd_796701 : Nat := 4983230072969 + 3 ^ 40 * 796701 * 2
def baseEnd_796701 : Nat := 409090550917792637373545

theorem tailTrace_796701 : CollatzResearch.WordTrace tailWord_796701 prefixEnd_796701 409090550917792637373545 := by
  unfold tailWord_796701
  simp only [CollatzResearch.WordTrace]
  refine ⟨29058072686695817543165957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19372048457797211695443971 29058072686695817543165957)
  ·
    refine ⟨5448388628755465789343617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29058072686695817543165957 5448388628755465789343617)
    ·
      refine ⟨4086291471566599342007713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5448388628755465789343617 4086291471566599342007713)
      ·
        refine ⟨3064718603674949506505785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4086291471566599342007713 3064718603674949506505785)
        ·
          refine ⟨2298538952756212129879339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3064718603674949506505785 2298538952756212129879339)
          ·
            refine ⟨3447808429134318194819009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2298538952756212129879339 3447808429134318194819009)
            ·
              refine ⟨2585856321850738646114257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3447808429134318194819009 2585856321850738646114257)
              ·
                refine ⟨1939392241388053984585693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2585856321850738646114257 1939392241388053984585693)
                ·
                  refine ⟨727272090520520244219635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1939392241388053984585693 727272090520520244219635)
                  ·
                    refine ⟨1090908135780780366329453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 727272090520520244219635 1090908135780780366329453)
                    ·
                      refine ⟨409090550917792637373545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1090908135780780366329453 409090550917792637373545)
                      ·
                        rfl

theorem cell23_796701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_796701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_796701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_796701 prefixEnd_796701 := by exact prefixLift 796701
  have htrace : WordTrace (prefixWord ++ tailWord_796701) baseStart_796701 baseEnd_796701 := by
    simpa [prefixWord, tailWord_796701, baseEnd_796701] using wordTrace_append hprefix tailTrace_796701
  have hstable : (prefixWord ++ tailWord_796701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796701).length < 2 ^ (prefixWord ++ tailWord_796701).sum := by decide
  have hdescent : baseEnd_796701 < baseStart_796701 := by decide
  rcases family_descends (prefixWord ++ tailWord_796701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796712 : List Nat := [2, 1, 5, 3, 2, 1, 1, 3, 1, 4]
def baseStart_796712 : Nat := 118140960795 + 796712 * 2 ^ 59
def prefixEnd_796712 : Nat := 4983230072969 + 3 ^ 40 * 796712 * 2
def baseEnd_796712 : Nat := 136365399734997364778665

theorem tailTrace_796712 : CollatzResearch.WordTrace tailWord_796712 prefixEnd_796712 136365399734997364778665 := by
  unfold tailWord_796712
  simp only [CollatzResearch.WordTrace]
  refine ⟨14529236944827983210908195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19372315926437310947877593 14529236944827983210908195)
  ·
    refine ⟨21793855417241974816362293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14529236944827983210908195 21793855417241974816362293)
    ·
      refine ⟨2043173945366435139033965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21793855417241974816362293 2043173945366435139033965)
      ·
        refine ⟨766190229512413177137737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2043173945366435139033965 766190229512413177137737)
        ·
          refine ⟨574642672134309882853303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 766190229512413177137737 574642672134309882853303)
          ·
            refine ⟨861964008201464824279955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 574642672134309882853303 861964008201464824279955)
            ·
              refine ⟨1292946012302197236419933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 861964008201464824279955 1292946012302197236419933)
              ·
                refine ⟨484854754613323963657475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1292946012302197236419933 484854754613323963657475)
                ·
                  refine ⟨727282131919985945486213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 484854754613323963657475 727282131919985945486213)
                  ·
                    refine ⟨136365399734997364778665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 727282131919985945486213 136365399734997364778665)
                    ·
                      rfl

theorem cell23_796712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_796712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_796712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_796712 prefixEnd_796712 := by exact prefixLift 796712
  have htrace : WordTrace (prefixWord ++ tailWord_796712) baseStart_796712 baseEnd_796712 := by
    simpa [prefixWord, tailWord_796712, baseEnd_796712] using wordTrace_append hprefix tailTrace_796712
  have hstable : (prefixWord ++ tailWord_796712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796712).length < 2 ^ (prefixWord ++ tailWord_796712).sum := by decide
  have hdescent : baseEnd_796712 < baseStart_796712 := by decide
  rcases family_descends (prefixWord ++ tailWord_796712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796727 : List Nat := [1, 1, 3, 1, 2, 2, 3, 3, 1, 1, 5]
def baseStart_796727 : Nat := 118140960795 + 796727 * 2 ^ 59
def prefixEnd_796727 : Nat := 4983230072969 + 3 ^ 40 * 796727 * 2
def baseEnd_796727 : Nat := 409103901414809535648425

theorem tailTrace_796727 : CollatzResearch.WordTrace tailWord_796727 prefixEnd_796727 409103901414809535648425 := by
  unfold tailWord_796727
  simp only [CollatzResearch.WordTrace]
  refine ⟨29059020984601623983612435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19372680656401082655741623 29059020984601623983612435)
  ·
    refine ⟨43588531476902435975418653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29059020984601623983612435 43588531476902435975418653)
    ·
      refine ⟨16345699303838413490781995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43588531476902435975418653 16345699303838413490781995)
      ·
        refine ⟨24518548955757620236172993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16345699303838413490781995 24518548955757620236172993)
        ·
          refine ⟨18388911716818215177129745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24518548955757620236172993 18388911716818215177129745)
          ·
            refine ⟨13791683787613661382847309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18388911716818215177129745 13791683787613661382847309)
            ·
              refine ⟨5171881420355123018567741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13791683787613661382847309 5171881420355123018567741)
              ·
                refine ⟨1939455532633171131962903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5171881420355123018567741 1939455532633171131962903)
                ·
                  refine ⟨2909183298949756697944355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1939455532633171131962903 2909183298949756697944355)
                  ·
                    refine ⟨4363774948424635046916533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2909183298949756697944355 4363774948424635046916533)
                    ·
                      refine ⟨409103901414809535648425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4363774948424635046916533 409103901414809535648425)
                      ·
                        rfl

theorem cell23_796727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 3, 1, 1, 5].length) (baseStart_796727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_796727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_796727 prefixEnd_796727 := by exact prefixLift 796727
  have htrace : WordTrace (prefixWord ++ tailWord_796727) baseStart_796727 baseEnd_796727 := by
    simpa [prefixWord, tailWord_796727, baseEnd_796727] using wordTrace_append hprefix tailTrace_796727
  have hstable : (prefixWord ++ tailWord_796727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796727).length < 2 ^ (prefixWord ++ tailWord_796727).sum := by decide
  have hdescent : baseEnd_796727 < baseStart_796727 := by decide
  rcases family_descends (prefixWord ++ tailWord_796727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796758 : List Nat := [5, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4]
def baseStart_796758 : Nat := 118140960795 + 796758 * 2 ^ 59
def prefixEnd_796758 : Nat := 4983230072969 + 3 ^ 40 * 796758 * 2
def baseEnd_796758 : Nat := 409119819315098914360783

theorem tailTrace_796758 : CollatzResearch.WordTrace tailWord_796758 prefixEnd_796758 409119819315098914360783 := by
  unfold tailWord_796758
  simp only [CollatzResearch.WordTrace]
  refine ⟨1816259477968082267374433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19373434431659544185327285 1816259477968082267374433)
  ·
    refine ⟨1362194608476061700530825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1816259477968082267374433 1362194608476061700530825)
    ·
      refine ⟨1021645956357046275398119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1362194608476061700530825 1021645956357046275398119)
      ·
        refine ⟨1532468934535569413097179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1021645956357046275398119 1532468934535569413097179)
        ·
          refine ⟨2298703401803354119645769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1532468934535569413097179 2298703401803354119645769)
          ·
            refine ⟨1724027551352515589734327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2298703401803354119645769 1724027551352515589734327)
            ·
              refine ⟨2586041327028773384601491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1724027551352515589734327 2586041327028773384601491)
              ·
                refine ⟨3879061990543160076902237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2586041327028773384601491 3879061990543160076902237)
                ·
                  refine ⟨1454648246453685028838339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3879061990543160076902237 1454648246453685028838339)
                  ·
                    refine ⟨2181972369680527543257509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1454648246453685028838339 2181972369680527543257509)
                    ·
                      refine ⟨409119819315098914360783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2181972369680527543257509 409119819315098914360783)
                      ·
                        rfl

theorem cell23_796758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_796758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_796758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_796758 prefixEnd_796758 := by exact prefixLift 796758
  have htrace : WordTrace (prefixWord ++ tailWord_796758) baseStart_796758 baseEnd_796758 := by
    simpa [prefixWord, tailWord_796758, baseEnd_796758] using wordTrace_append hprefix tailTrace_796758
  have hstable : (prefixWord ++ tailWord_796758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796758).length < 2 ^ (prefixWord ++ tailWord_796758).sum := by decide
  have hdescent : baseEnd_796758 < baseStart_796758 := by decide
  rcases family_descends (prefixWord ++ tailWord_796758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796778 : List Nat := [3, 1, 3, 2, 4, 1, 1, 1, 1, 1, 5]
def baseStart_796778 : Nat := 118140960795 + 796778 * 2 ^ 59
def prefixEnd_796778 : Nat := 4983230072969 + 3 ^ 40 * 796778 * 2
def baseEnd_796778 : Nat := 409130088928188836110691

theorem tailTrace_796778 : CollatzResearch.WordTrace tailWord_796778 prefixEnd_796778 409130088928188836110691 := by
  unfold tailWord_796778
  simp only [CollatzResearch.WordTrace]
  refine ⟨7265220276854214923429747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19373920738277906462479325 7265220276854214923429747)
  ·
    refine ⟨10897830415281322385144621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7265220276854214923429747 10897830415281322385144621)
    ·
      refine ⟨4086686405730495894429233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10897830415281322385144621 4086686405730495894429233)
      ·
        refine ⟨3065014804297871920821925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4086686405730495894429233 3065014804297871920821925)
        ·
          refine ⟨574690275805850985154111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3065014804297871920821925 574690275805850985154111)
          ·
            refine ⟨862035413708776477731167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 574690275805850985154111 862035413708776477731167)
            ·
              refine ⟨1293053120563164716596751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 862035413708776477731167 1293053120563164716596751)
              ·
                refine ⟨1939579680844747074895127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1293053120563164716596751 1939579680844747074895127)
                ·
                  refine ⟨2909369521267120612342691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1939579680844747074895127 2909369521267120612342691)
                  ·
                    refine ⟨4364054281900680918514037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2909369521267120612342691 4364054281900680918514037)
                    ·
                      refine ⟨409130088928188836110691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4364054281900680918514037 409130088928188836110691)
                      ·
                        rfl

theorem cell23_796778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_796778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_796778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_796778 prefixEnd_796778 := by exact prefixLift 796778
  have htrace : WordTrace (prefixWord ++ tailWord_796778) baseStart_796778 baseEnd_796778 := by
    simpa [prefixWord, tailWord_796778, baseEnd_796778] using wordTrace_append hprefix tailTrace_796778
  have hstable : (prefixWord ++ tailWord_796778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796778).length < 2 ^ (prefixWord ++ tailWord_796778).sum := by decide
  have hdescent : baseEnd_796778 < baseStart_796778 := by decide
  rcases family_descends (prefixWord ++ tailWord_796778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796791 : List Nat := [1, 1, 3, 1, 1, 5, 1, 4, 2, 1, 3]
def baseStart_796791 : Nat := 118140960795 + 796791 * 2 ^ 59
def prefixEnd_796791 : Nat := 4983230072969 + 3 ^ 40 * 796791 * 2
def baseEnd_796791 : Nat := 409136764176697285248131

theorem tailTrace_796791 : CollatzResearch.WordTrace tailWord_796791 prefixEnd_796791 409136764176697285248131 := by
  unfold tailWord_796791
  simp only [CollatzResearch.WordTrace]
  refine ⟨29061355256369762913942227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19374236837579841942628151 29061355256369762913942227)
  ·
    refine ⟨43592032884554644370913341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29061355256369762913942227 43592032884554644370913341)
    ·
      refine ⟨16347012331707991639092503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43592032884554644370913341 16347012331707991639092503)
      ·
        refine ⟨24520518497561987458638755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16347012331707991639092503 24520518497561987458638755)
        ·
          refine ⟨36780777746342981187958133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24520518497561987458638755 36780777746342981187958133)
          ·
            refine ⟨3448197913719654486371075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36780777746342981187958133 3448197913719654486371075)
            ·
              refine ⟨5172296870579481729556613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3448197913719654486371075 5172296870579481729556613)
              ·
                refine ⟨969805663233652824291865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5172296870579481729556613 969805663233652824291865)
                ·
                  refine ⟨727354247425239618218899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 969805663233652824291865 727354247425239618218899)
                  ·
                    refine ⟨1091031371137859427328349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 727354247425239618218899 1091031371137859427328349)
                    ·
                      refine ⟨409136764176697285248131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1091031371137859427328349 409136764176697285248131)
                      ·
                        rfl

theorem cell23_796791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 4, 2, 1, 3].length) (baseStart_796791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_796791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_796791 prefixEnd_796791 := by exact prefixLift 796791
  have htrace : WordTrace (prefixWord ++ tailWord_796791) baseStart_796791 baseEnd_796791 := by
    simpa [prefixWord, tailWord_796791, baseEnd_796791] using wordTrace_append hprefix tailTrace_796791
  have hstable : (prefixWord ++ tailWord_796791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796791).length < 2 ^ (prefixWord ++ tailWord_796791).sum := by decide
  have hdescent : baseEnd_796791 < baseStart_796791 := by decide
  rcases family_descends (prefixWord ++ tailWord_796791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796807 : List Nat := [1, 1, 4, 2, 1, 1, 3, 1, 1, 8]
def baseStart_796807 : Nat := 118140960795 + 796807 * 2 ^ 59
def prefixEnd_796807 : Nat := 4983230072969 + 3 ^ 40 * 796807 * 2
def baseEnd_796807 : Nat := 136381659955723074216019

theorem tailTrace_796807 : CollatzResearch.WordTrace tailWord_796807 prefixEnd_796807 136381659955723074216019 := by
  unfold tailWord_796807
  simp only [CollatzResearch.WordTrace]
  refine ⟨29061938824311797646524675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19374625882874531764349783 29061938824311797646524675)
  ·
    refine ⟨43592908236467696469787013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29061938824311797646524675 43592908236467696469787013)
    ·
      refine ⟨8173670294337693088085065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43592908236467696469787013 8173670294337693088085065)
      ·
        refine ⟨6130252720753269816063799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8173670294337693088085065 6130252720753269816063799)
        ·
          refine ⟨9195379081129904724095699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6130252720753269816063799 9195379081129904724095699)
          ·
            refine ⟨13793068621694857086143549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9195379081129904724095699 13793068621694857086143549)
            ·
              refine ⟨5172400733135571407303831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13793068621694857086143549 5172400733135571407303831)
              ·
                refine ⟨7758601099703357110955747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5172400733135571407303831 7758601099703357110955747)
                ·
                  refine ⟨11637901649555035666433621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7758601099703357110955747 11637901649555035666433621)
                  ·
                    refine ⟨136381659955723074216019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 11637901649555035666433621 136381659955723074216019)
                    ·
                      rfl

theorem cell23_796807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 8].length) (baseStart_796807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_796807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_796807 prefixEnd_796807 := by exact prefixLift 796807
  have htrace : WordTrace (prefixWord ++ tailWord_796807) baseStart_796807 baseEnd_796807 := by
    simpa [prefixWord, tailWord_796807, baseEnd_796807] using wordTrace_append hprefix tailTrace_796807
  have hstable : (prefixWord ++ tailWord_796807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796807).length < 2 ^ (prefixWord ++ tailWord_796807).sum := by decide
  have hdescent : baseEnd_796807 < baseStart_796807 := by decide
  rcases family_descends (prefixWord ++ tailWord_796807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796808 : List Nat := [2, 1, 3, 4, 1, 1, 2, 3, 2, 1, 3]
def baseStart_796808 : Nat := 118140960795 + 796808 * 2 ^ 59
def prefixEnd_796808 : Nat := 4983230072969 + 3 ^ 40 * 796808 * 2
def baseEnd_796808 : Nat := 409145493347823718735553

theorem tailTrace_796808 : CollatzResearch.WordTrace tailWord_796808 prefixEnd_796808 409145493347823718735553 := by
  unfold tailWord_796808
  simp only [CollatzResearch.WordTrace]
  refine ⟨14530987648654087408655539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19374650198205449878207385 14530987648654087408655539)
  ·
    refine ⟨21796481472981131112983309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14530987648654087408655539 21796481472981131112983309)
    ·
      refine ⟨8173680552367924167368741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21796481472981131112983309 8173680552367924167368741)
      ·
        refine ⟨1532565103568985781381639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8173680552367924167368741 1532565103568985781381639)
        ·
          refine ⟨2298847655353478672072459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1532565103568985781381639 2298847655353478672072459)
          ·
            refine ⟨3448271483030218008108689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2298847655353478672072459 3448271483030218008108689)
            ·
              refine ⟨2586203612272663506081517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3448271483030218008108689 2586203612272663506081517)
              ·
                refine ⟨969826354602248814780569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2586203612272663506081517 969826354602248814780569)
                ·
                  refine ⟨727369765951686611085427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 969826354602248814780569 727369765951686611085427)
                  ·
                    refine ⟨1091054648927529916628141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 727369765951686611085427 1091054648927529916628141)
                    ·
                      refine ⟨409145493347823718735553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1091054648927529916628141 409145493347823718735553)
                      ·
                        rfl

theorem cell23_796808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_796808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_796808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_796808 prefixEnd_796808 := by exact prefixLift 796808
  have htrace : WordTrace (prefixWord ++ tailWord_796808) baseStart_796808 baseEnd_796808 := by
    simpa [prefixWord, tailWord_796808, baseEnd_796808] using wordTrace_append hprefix tailTrace_796808
  have hstable : (prefixWord ++ tailWord_796808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796808).length < 2 ^ (prefixWord ++ tailWord_796808).sum := by decide
  have hdescent : baseEnd_796808 < baseStart_796808 := by decide
  rcases family_descends (prefixWord ++ tailWord_796808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796818 : List Nat := [3, 2, 3, 1, 1, 1, 2, 4, 1, 3, 2]
def baseStart_796818 : Nat := 118140960795 + 796818 * 2 ^ 59
def prefixEnd_796818 : Nat := 4983230072969 + 3 ^ 40 * 796818 * 2
def baseEnd_796818 : Nat := 409150628154368679610507

theorem tailTrace_796818 : CollatzResearch.WordTrace tailWord_796818 prefixEnd_796818 409150628154368679610507 := by
  unfold tailWord_796818
  simp only [CollatzResearch.WordTrace]
  refine ⟨7265585006817986631293777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19374893351514631016783405 7265585006817986631293777)
  ·
    refine ⟨5449188755113489973470333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7265585006817986631293777 5449188755113489973470333)
    ·
      refine ⟨2043445783167558740051375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5449188755113489973470333 2043445783167558740051375)
      ·
        refine ⟨3065168674751338110077063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2043445783167558740051375 3065168674751338110077063)
        ·
          refine ⟨4597753012127007165115595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3065168674751338110077063 4597753012127007165115595)
          ·
            refine ⟨6896629518190510747673393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4597753012127007165115595 6896629518190510747673393)
            ·
              refine ⟨5172472138642883060755045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6896629518190510747673393 5172472138642883060755045)
              ·
                refine ⟨969838525995540573891571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5172472138642883060755045 969838525995540573891571)
                ·
                  refine ⟨1454757788993310860837357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 969838525995540573891571 1454757788993310860837357)
                  ·
                    refine ⟨545534170872491572814009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1454757788993310860837357 545534170872491572814009)
                    ·
                      refine ⟨409150628154368679610507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 545534170872491572814009 409150628154368679610507)
                      ·
                        rfl

theorem cell23_796818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_796818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_796818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_796818 prefixEnd_796818 := by exact prefixLift 796818
  have htrace : WordTrace (prefixWord ++ tailWord_796818) baseStart_796818 baseEnd_796818 := by
    simpa [prefixWord, tailWord_796818, baseEnd_796818] using wordTrace_append hprefix tailTrace_796818
  have hstable : (prefixWord ++ tailWord_796818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796818).length < 2 ^ (prefixWord ++ tailWord_796818).sum := by decide
  have hdescent : baseEnd_796818 < baseStart_796818 := by decide
  rcases family_descends (prefixWord ++ tailWord_796818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796827 : List Nat := [1, 1, 1, 1, 1, 1, 2, 6, 1, 4, 4]
def baseStart_796827 : Nat := 118140960795 + 796827 * 2 ^ 59
def prefixEnd_796827 : Nat := 4983230072969 + 3 ^ 40 * 796827 * 2
def baseEnd_796827 : Nat := 409155249480259144397965

theorem tailTrace_796827 : CollatzResearch.WordTrace tailWord_796827 prefixEnd_796827 409155249480259144397965 := by
  unfold tailWord_796827
  simp only [CollatzResearch.WordTrace]
  refine ⟨29062668284239341062252735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19375112189492894041501823 29062668284239341062252735)
  ·
    refine ⟨43594002426359011593379103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29062668284239341062252735 43594002426359011593379103)
    ·
      refine ⟨65391003639538517390068655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43594002426359011593379103 65391003639538517390068655)
      ·
        refine ⟨98086505459307776085102983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65391003639538517390068655 98086505459307776085102983)
        ·
          refine ⟨147129758188961664127654475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98086505459307776085102983 147129758188961664127654475)
          ·
            refine ⟨220694637283442496191481713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147129758188961664127654475 220694637283442496191481713)
            ·
              refine ⟨165520977962581872143611285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 220694637283442496191481713 165520977962581872143611285)
              ·
                refine ⟨7758795841996025256731779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 165520977962581872143611285 7758795841996025256731779)
                ·
                  refine ⟨11638193762994037885097669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7758795841996025256731779 11638193762994037885097669)
                  ·
                    refine ⟨2182161330561382103455813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11638193762994037885097669 2182161330561382103455813)
                    ·
                      refine ⟨409155249480259144397965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2182161330561382103455813 409155249480259144397965)
                      ·
                        rfl

theorem cell23_796827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 4, 4].length) (baseStart_796827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_796827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_796827 prefixEnd_796827 := by exact prefixLift 796827
  have htrace : WordTrace (prefixWord ++ tailWord_796827) baseStart_796827 baseEnd_796827 := by
    simpa [prefixWord, tailWord_796827, baseEnd_796827] using wordTrace_append hprefix tailTrace_796827
  have hstable : (prefixWord ++ tailWord_796827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796827).length < 2 ^ (prefixWord ++ tailWord_796827).sum := by decide
  have hdescent : baseEnd_796827 < baseStart_796827 := by decide
  rcases family_descends (prefixWord ++ tailWord_796827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796837 : List Nat := [1, 3, 1, 2, 1, 3, 1, 2, 9]
def baseStart_796837 : Nat := 118140960795 + 796837 * 2 ^ 59
def prefixEnd_796837 : Nat := 4983230072969 + 3 ^ 40 * 796837 * 2
def baseEnd_796837 : Nat := 45462264920756011696991

theorem tailTrace_796837 : CollatzResearch.WordTrace tailWord_796837 prefixEnd_796837 45462264920756011696991 := by
  unfold tailWord_796837
  simp only [CollatzResearch.WordTrace]
  refine ⟨29063033014203112770116765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19375355342802075180077843 29063033014203112770116765)
  ·
    refine ⟨10898637380326167288793787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29063033014203112770116765 10898637380326167288793787)
    ·
      refine ⟨16347956070489250933190681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10898637380326167288793787 16347956070489250933190681)
      ·
        refine ⟨12260967052866938199893011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16347956070489250933190681 12260967052866938199893011)
        ·
          refine ⟨18391450579300407299839517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12260967052866938199893011 18391450579300407299839517)
          ·
            refine ⟨6896793967237652737439819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18391450579300407299839517 6896793967237652737439819)
            ·
              refine ⟨10345190950856479106159729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6896793967237652737439819 10345190950856479106159729)
              ·
                refine ⟨7758893213142359329619797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10345190950856479106159729 7758893213142359329619797)
                ·
                  refine ⟨45462264920756011696991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 7758893213142359329619797 45462264920756011696991)
                  ·
                    rfl

theorem cell23_796837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 9].length) (baseStart_796837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_796837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_796837 prefixEnd_796837 := by exact prefixLift 796837
  have htrace : WordTrace (prefixWord ++ tailWord_796837) baseStart_796837 baseEnd_796837 := by
    simpa [prefixWord, tailWord_796837, baseEnd_796837] using wordTrace_append hprefix tailTrace_796837
  have hstable : (prefixWord ++ tailWord_796837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796837).length < 2 ^ (prefixWord ++ tailWord_796837).sum := by decide
  have hdescent : baseEnd_796837 < baseStart_796837 := by decide
  rcases family_descends (prefixWord ++ tailWord_796837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796842 : List Nat := [3, 1, 5, 1, 2, 2, 1, 2, 2, 1, 3]
def baseStart_796842 : Nat := 118140960795 + 796842 * 2 ^ 59
def prefixEnd_796842 : Nat := 4983230072969 + 3 ^ 40 * 796842 * 2
def baseEnd_796842 : Nat := 409162951690076585710397

theorem tailTrace_796842 : CollatzResearch.WordTrace tailWord_796842 prefixEnd_796842 409162951690076585710397 := by
  unfold tailWord_796842
  simp only [CollatzResearch.WordTrace]
  refine ⟨7265803844796249656012195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19375476919456665749365853 7265803844796249656012195)
  ·
    refine ⟨10898705767194374484018293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7265803844796249656012195 10898705767194374484018293)
    ·
      refine ⟨1021753665674472607876715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10898705767194374484018293 1021753665674472607876715)
      ·
        refine ⟨1532630498511708911815073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1021753665674472607876715 1532630498511708911815073)
        ·
          refine ⟨1149472873883781683861305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1532630498511708911815073 1149472873883781683861305)
          ·
            refine ⟨862104655412836262895979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1149472873883781683861305 862104655412836262895979)
            ·
              refine ⟨1293156983119254394343969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 862104655412836262895979 1293156983119254394343969)
              ·
                refine ⟨969867737339440795757977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1293156983119254394343969 969867737339440795757977)
                ·
                  refine ⟨727400803004580596818483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 969867737339440795757977 727400803004580596818483)
                  ·
                    refine ⟨1091101204506870895227725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 727400803004580596818483 1091101204506870895227725)
                    ·
                      refine ⟨409162951690076585710397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1091101204506870895227725 409162951690076585710397)
                      ·
                        rfl

theorem cell23_796842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_796842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_796842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_796842 prefixEnd_796842 := by exact prefixLift 796842
  have htrace : WordTrace (prefixWord ++ tailWord_796842) baseStart_796842 baseEnd_796842 := by
    simpa [prefixWord, tailWord_796842, baseEnd_796842] using wordTrace_append hprefix tailTrace_796842
  have hstable : (prefixWord ++ tailWord_796842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796842).length < 2 ^ (prefixWord ++ tailWord_796842).sum := by decide
  have hdescent : baseEnd_796842 < baseStart_796842 := by decide
  rcases family_descends (prefixWord ++ tailWord_796842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796888 : List Nat := [2, 1, 2, 2, 4, 3, 1, 3, 5]
def baseStart_796888 : Nat := 118140960795 + 796888 * 2 ^ 59
def prefixEnd_796888 : Nat := 4983230072969 + 3 ^ 40 * 796888 * 2
def baseEnd_796888 : Nat := 45465174644464822859465

theorem tailTrace_796888 : CollatzResearch.WordTrace tailWord_796888 prefixEnd_796888 45465174644464822859465 := by
  unfold tailWord_796888
  simp only [CollatzResearch.WordTrace]
  refine ⟨14532446568509174240111659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19376595424678898986815545 14532446568509174240111659)
  ·
    refine ⟨21798669852763761360167489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14532446568509174240111659 21798669852763761360167489)
    ·
      refine ⟨16349002389572821020125617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21798669852763761360167489 16349002389572821020125617)
      ·
        refine ⟨12261751792179615765094213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16349002389572821020125617 12261751792179615765094213)
        ·
          refine ⟨2299078461033677955955165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12261751792179615765094213 2299078461033677955955165)
          ·
            refine ⟨862154422887629233483187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2299078461033677955955165 862154422887629233483187)
            ·
              refine ⟨1293231634331443850224781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 862154422887629233483187 1293231634331443850224781)
              ·
                refine ⟨484961862874291443834293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1293231634331443850224781 484961862874291443834293)
                ·
                  refine ⟨45465174644464822859465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 484961862874291443834293 45465174644464822859465)
                  ·
                    rfl

theorem cell23_796888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 3, 5].length) (baseStart_796888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_796888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_796888 prefixEnd_796888 := by exact prefixLift 796888
  have htrace : WordTrace (prefixWord ++ tailWord_796888) baseStart_796888 baseEnd_796888 := by
    simpa [prefixWord, tailWord_796888, baseEnd_796888] using wordTrace_append hprefix tailTrace_796888
  have hstable : (prefixWord ++ tailWord_796888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796888).length < 2 ^ (prefixWord ++ tailWord_796888).sum := by decide
  have hdescent : baseEnd_796888 < baseStart_796888 := by decide
  rcases family_descends (prefixWord ++ tailWord_796888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796901 : List Nat := [1, 3, 1, 4, 2, 2, 1, 2, 2, 5]
def baseStart_796901 : Nat := 118140960795 + 796901 * 2 ^ 59
def prefixEnd_796901 : Nat := 4983230072969 + 3 ^ 40 * 796901 * 2
def baseEnd_796901 : Nat := 136397749016230618290875

theorem tailTrace_796901 : CollatzResearch.WordTrace tailWord_796901 prefixEnd_796901 136397749016230618290875 := by
  unfold tailWord_796901
  simp only [CollatzResearch.WordTrace]
  refine ⟨29065367285971251700446557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19376911523980834466964371 29065367285971251700446557)
  ·
    refine ⟨10899512732239219387667459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29065367285971251700446557 10899512732239219387667459)
    ·
      refine ⟨16349269098358829081501189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10899512732239219387667459 16349269098358829081501189)
      ·
        refine ⟨3065487955942280452781473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16349269098358829081501189 3065487955942280452781473)
        ·
          refine ⟨2299115966956710339586105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3065487955942280452781473 2299115966956710339586105)
          ·
            refine ⟨1724336975217532754689579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2299115966956710339586105 1724336975217532754689579)
            ·
              refine ⟨2586505462826299132034369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1724336975217532754689579 2586505462826299132034369)
              ·
                refine ⟨1939879097119724349025777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2586505462826299132034369 1939879097119724349025777)
                ·
                  refine ⟨1454909322839793261769333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1939879097119724349025777 1454909322839793261769333)
                  ·
                    refine ⟨136397749016230618290875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1454909322839793261769333 136397749016230618290875)
                    ·
                      rfl

theorem cell23_796901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 2, 2, 5].length) (baseStart_796901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_796901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_796901 prefixEnd_796901 := by exact prefixLift 796901
  have htrace : WordTrace (prefixWord ++ tailWord_796901) baseStart_796901 baseEnd_796901 := by
    simpa [prefixWord, tailWord_796901, baseEnd_796901] using wordTrace_append hprefix tailTrace_796901
  have hstable : (prefixWord ++ tailWord_796901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796901).length < 2 ^ (prefixWord ++ tailWord_796901).sum := by decide
  have hdescent : baseEnd_796901 < baseStart_796901 := by decide
  rcases family_descends (prefixWord ++ tailWord_796901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796965 : List Nat := [1, 3, 1, 2, 5, 1, 1, 4, 1, 4]
def baseStart_796965 : Nat := 118140960795 + 796965 * 2 ^ 59
def prefixEnd_796965 : Nat := 4983230072969 + 3 ^ 40 * 796965 * 2
def baseEnd_796965 : Nat := 136408703270193201490777

theorem tailTrace_796965 : CollatzResearch.WordTrace tailWord_796965 prefixEnd_796965 136408703270193201490777 := by
  unfold tailWord_796965
  simp only [CollatzResearch.WordTrace]
  refine ⟨29067701557739390630776349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19378467705159593753850899 29067701557739390630776349)
  ·
    refine ⟨10900388084152271486541131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29067701557739390630776349 10900388084152271486541131)
    ·
      refine ⟨16350582126228407229811697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10900388084152271486541131 16350582126228407229811697)
      ·
        refine ⟨12262936594671305422358773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16350582126228407229811697 12262936594671305422358773)
        ·
          refine ⟨1149650305750434883346135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12262936594671305422358773 1149650305750434883346135)
          ·
            refine ⟨1724475458625652325019203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1149650305750434883346135 1724475458625652325019203)
            ·
              refine ⟨2586713187938478487528805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1724475458625652325019203 2586713187938478487528805)
              ·
                refine ⟨485008722738464716411651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2586713187938478487528805 485008722738464716411651)
                ·
                  refine ⟨727513084107697074617477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 485008722738464716411651 727513084107697074617477)
                  ·
                    refine ⟨136408703270193201490777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 727513084107697074617477 136408703270193201490777)
                    ·
                      rfl

theorem cell23_796965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 4, 1, 4].length) (baseStart_796965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_796965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_796965 prefixEnd_796965 := by exact prefixLift 796965
  have htrace : WordTrace (prefixWord ++ tailWord_796965) baseStart_796965 baseEnd_796965 := by
    simpa [prefixWord, tailWord_796965, baseEnd_796965] using wordTrace_append hprefix tailTrace_796965
  have hstable : (prefixWord ++ tailWord_796965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796965).length < 2 ^ (prefixWord ++ tailWord_796965).sum := by decide
  have hdescent : baseEnd_796965 < baseStart_796965 := by decide
  rcases family_descends (prefixWord ++ tailWord_796965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796988 : List Nat := [2, 2, 2, 2, 1, 2, 3, 2, 3, 1, 3]
def baseStart_796988 : Nat := 118140960795 + 796988 * 2 ^ 59
def prefixEnd_796988 : Nat := 4983230072969 + 3 ^ 40 * 796988 * 2
def baseEnd_796988 : Nat := 409237919865633014484725

theorem tailTrace_796988 : CollatzResearch.WordTrace tailWord_796988 prefixEnd_796988 409237919865633014484725 := by
  unfold tailWord_796988
  simp only [CollatzResearch.WordTrace]
  refine ⟨14534270218328032779431809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19379026957770710372575745 14534270218328032779431809)
  ·
    refine ⟨10900702663746024584573857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14534270218328032779431809 10900702663746024584573857)
    ·
      refine ⟨8175526997809518438430393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10900702663746024584573857 8175526997809518438430393)
      ·
        refine ⟨6131645248357138828822795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8175526997809518438430393 6131645248357138828822795)
        ·
          refine ⟨9197467872535708243234193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6131645248357138828822795 9197467872535708243234193)
          ·
            refine ⟨6898100904401781182425645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9197467872535708243234193 6898100904401781182425645)
            ·
              refine ⟨2586787839150667943409617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6898100904401781182425645 2586787839150667943409617)
              ·
                refine ⟨1940090879363000957557213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2586787839150667943409617 1940090879363000957557213)
                ·
                  refine ⟨727534079761125359083955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1940090879363000957557213 727534079761125359083955)
                  ·
                    refine ⟨1091301119641688038625933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 727534079761125359083955 1091301119641688038625933)
                    ·
                      refine ⟨409237919865633014484725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1091301119641688038625933 409237919865633014484725)
                      ·
                        rfl

theorem cell23_796988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 2, 3, 1, 3].length) (baseStart_796988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_796988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_796988 prefixEnd_796988 := by exact prefixLift 796988
  have htrace : WordTrace (prefixWord ++ tailWord_796988) baseStart_796988 baseEnd_796988 := by
    simpa [prefixWord, tailWord_796988, baseEnd_796988] using wordTrace_append hprefix tailTrace_796988
  have hstable : (prefixWord ++ tailWord_796988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796988).length < 2 ^ (prefixWord ++ tailWord_796988).sum := by decide
  have hdescent : baseEnd_796988 < baseStart_796988 := by decide
  rcases family_descends (prefixWord ++ tailWord_796988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796991 : List Nat := [1, 1, 2, 2, 4, 1, 2, 4, 1, 5]
def baseStart_796991 : Nat := 118140960795 + 796991 * 2 ^ 59
def prefixEnd_796991 : Nat := 4983230072969 + 3 ^ 40 * 796991 * 2
def baseEnd_796991 : Nat := 136413153435865500915737

theorem tailTrace_796991 : CollatzResearch.WordTrace tailWord_796991 prefixEnd_796991 136413153435865500915737 := by
  unfold tailWord_796991
  simp only [CollatzResearch.WordTrace]
  refine ⟨29068649855645197071222827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19379099903763464714148551 29068649855645197071222827)
  ·
    refine ⟨43602974783467795606834241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29068649855645197071222827 43602974783467795606834241)
    ·
      refine ⟨32702231087600846705125681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43602974783467795606834241 32702231087600846705125681)
      ·
        refine ⟨24526673315700635028844261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32702231087600846705125681 24526673315700635028844261)
        ·
          refine ⟨4598751246693869067908299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24526673315700635028844261 4598751246693869067908299)
          ·
            refine ⟨6898126870040803601862449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4598751246693869067908299 6898126870040803601862449)
            ·
              refine ⟨5173595152530602701396837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6898126870040803601862449 5173595152530602701396837)
              ·
                refine ⟨970049091099488006511907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5173595152530602701396837 970049091099488006511907)
                ·
                  refine ⟨1455073636649232009767861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 970049091099488006511907 1455073636649232009767861)
                  ·
                    refine ⟨136413153435865500915737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1455073636649232009767861 136413153435865500915737)
                    ·
                      rfl

theorem cell23_796991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 4, 1, 5].length) (baseStart_796991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_796991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_796991 prefixEnd_796991 := by exact prefixLift 796991
  have htrace : WordTrace (prefixWord ++ tailWord_796991) baseStart_796991 baseEnd_796991 := by
    simpa [prefixWord, tailWord_796991, baseEnd_796991] using wordTrace_append hprefix tailTrace_796991
  have hstable : (prefixWord ++ tailWord_796991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796991).length < 2 ^ (prefixWord ++ tailWord_796991).sum := by decide
  have hdescent : baseEnd_796991 < baseStart_796991 := by decide
  rcases family_descends (prefixWord ++ tailWord_796991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797008 : List Nat := [2, 1, 1, 1, 1, 6, 4, 1, 1, 5]
def baseStart_797008 : Nat := 118140960795 + 797008 * 2 ^ 59
def prefixEnd_797008 : Nat := 4983230072969 + 3 ^ 40 * 797008 * 2
def baseEnd_797008 : Nat := 136416063159574312078211

theorem tailTrace_797008 : CollatzResearch.WordTrace tailWord_797008 prefixEnd_797008 136416063159574312078211 := by
  unfold tailWord_797008
  simp only [CollatzResearch.WordTrace]
  refine ⟨14534634948291804487295839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19379513264389072649727785 14534634948291804487295839)
  ·
    refine ⟨21801952422437706730943759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14534634948291804487295839 21801952422437706730943759)
    ·
      refine ⟨32702928633656560096415639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21801952422437706730943759 32702928633656560096415639)
      ·
        refine ⟨49054392950484840144623459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32702928633656560096415639 49054392950484840144623459)
        ·
          refine ⟨73581589425727260216935189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49054392950484840144623459 73581589425727260216935189)
          ·
            refine ⟨3449137004330965322668837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 73581589425727260216935189 3449137004330965322668837)
            ·
              refine ⟨646713188312055998000407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3449137004330965322668837 646713188312055998000407)
              ·
                refine ⟨970069782468083997000611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 646713188312055998000407 970069782468083997000611)
                ·
                  refine ⟨1455104673702125995500917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 970069782468083997000611 1455104673702125995500917)
                  ·
                    refine ⟨136416063159574312078211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1455104673702125995500917 136416063159574312078211)
                    ·
                      rfl

theorem cell23_797008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 4, 1, 1, 5].length) (baseStart_797008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_797008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_797008 prefixEnd_797008 := by exact prefixLift 797008
  have htrace : WordTrace (prefixWord ++ tailWord_797008) baseStart_797008 baseEnd_797008 := by
    simpa [prefixWord, tailWord_797008, baseEnd_797008] using wordTrace_append hprefix tailTrace_797008
  have hstable : (prefixWord ++ tailWord_797008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797008).length < 2 ^ (prefixWord ++ tailWord_797008).sum := by decide
  have hdescent : baseEnd_797008 < baseStart_797008 := by decide
  rcases family_descends (prefixWord ++ tailWord_797008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797031 : List Nat := [1, 1, 5, 1, 3, 1, 1, 1, 3, 1, 5]
def baseStart_797031 : Nat := 118140960795 + 797031 * 2 ^ 59
def prefixEnd_797031 : Nat := 4983230072969 + 3 ^ 40 * 797031 * 2
def baseEnd_797031 : Nat := 409259999533776346247027

theorem tailTrace_797031 : CollatzResearch.WordTrace tailWord_797031 prefixEnd_797031 409259999533776346247027 := by
  unfold tailWord_797031
  simp only [CollatzResearch.WordTrace]
  refine ⟨29070108775500283902678947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19380072517000189268452631 29070108775500283902678947)
  ·
    refine ⟨43605163163250425854018421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29070108775500283902678947 43605163163250425854018421)
    ·
      refine ⟨4087984046554727423814227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43605163163250425854018421 4087984046554727423814227)
      ·
        refine ⟨6131976069832091135721341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4087984046554727423814227 6131976069832091135721341)
        ·
          refine ⟨2299491026187034175895503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6131976069832091135721341 2299491026187034175895503)
          ·
            refine ⟨3449236539280551263843255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2299491026187034175895503 3449236539280551263843255)
            ·
              refine ⟨5173854808920826895764883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3449236539280551263843255 5173854808920826895764883)
              ·
                refine ⟨7760782213381240343647325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5173854808920826895764883 7760782213381240343647325)
                ·
                  refine ⟨2910293330017965128867747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7760782213381240343647325 2910293330017965128867747)
                  ·
                    refine ⟨4365439995026947693301621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2910293330017965128867747 4365439995026947693301621)
                    ·
                      refine ⟨409259999533776346247027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4365439995026947693301621 409259999533776346247027)
                      ·
                        rfl

theorem cell23_797031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_797031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_797031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_797031 prefixEnd_797031 := by exact prefixLift 797031
  have htrace : WordTrace (prefixWord ++ tailWord_797031) baseStart_797031 baseEnd_797031 := by
    simpa [prefixWord, tailWord_797031, baseEnd_797031] using wordTrace_append hprefix tailTrace_797031
  have hstable : (prefixWord ++ tailWord_797031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797031).length < 2 ^ (prefixWord ++ tailWord_797031).sum := by decide
  have hdescent : baseEnd_797031 < baseStart_797031 := by decide
  rcases family_descends (prefixWord ++ tailWord_797031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797045 : List Nat := [1, 3, 4, 1, 2, 2, 2, 2, 1, 1, 4]
def baseStart_797045 : Nat := 118140960795 + 797045 * 2 ^ 59
def prefixEnd_797045 : Nat := 4983230072969 + 3 ^ 40 * 797045 * 2
def baseEnd_797045 : Nat := 409267188262939291471963

theorem tailTrace_797045 : CollatzResearch.WordTrace tailWord_797045 prefixEnd_797045 409267188262939291471963 := by
  unfold tailWord_797045
  simp only [CollatzResearch.WordTrace]
  refine ⟨29070619397449564293688589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19380412931633042862459059 29070619397449564293688589)
  ·
    refine ⟨10901482274043586610133221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29070619397449564293688589 10901482274043586610133221)
    ·
      refine ⟨2044027926383172489399979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10901482274043586610133221 2044027926383172489399979)
      ·
        refine ⟨3066041889574758734099969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2044027926383172489399979 3066041889574758734099969)
        ·
          refine ⟨2299531417181069050574977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3066041889574758734099969 2299531417181069050574977)
          ·
            refine ⟨1724648562885801787931233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2299531417181069050574977 1724648562885801787931233)
            ·
              refine ⟨1293486422164351340948425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1724648562885801787931233 1293486422164351340948425)
              ·
                refine ⟨970114816623263505711319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1293486422164351340948425 970114816623263505711319)
                ·
                  refine ⟨1455172224934895258566979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 970114816623263505711319 1455172224934895258566979)
                  ·
                    refine ⟨2182758337402342887850469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1455172224934895258566979 2182758337402342887850469)
                    ·
                      refine ⟨409267188262939291471963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2182758337402342887850469 409267188262939291471963)
                      ·
                        rfl

theorem cell23_797045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_797045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_797045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_797045 prefixEnd_797045 := by exact prefixLift 797045
  have htrace : WordTrace (prefixWord ++ tailWord_797045) baseStart_797045 baseEnd_797045 := by
    simpa [prefixWord, tailWord_797045, baseEnd_797045] using wordTrace_append hprefix tailTrace_797045
  have hstable : (prefixWord ++ tailWord_797045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797045).length < 2 ^ (prefixWord ++ tailWord_797045).sum := by decide
  have hdescent : baseEnd_797045 < baseStart_797045 := by decide
  rcases family_descends (prefixWord ++ tailWord_797045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797051 : List Nat := [1, 1, 1, 1, 1, 7, 4, 7]
def baseStart_797051 : Nat := 118140960795 + 797051 * 2 ^ 59
def prefixEnd_797051 : Nat := 4983230072969 + 3 ^ 40 * 797051 * 2
def baseEnd_797051 : Nat := 15158158116550602518405

theorem tailTrace_797051 : CollatzResearch.WordTrace tailWord_797051 prefixEnd_797051 15158158116550602518405 := by
  unfold tailWord_797051
  simp only [CollatzResearch.WordTrace]
  refine ⟨29070838235427827318407007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19380558823618551545604671 29070838235427827318407007)
  ·
    refine ⟨43606257353141740977610511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29070838235427827318407007 43606257353141740977610511)
    ·
      refine ⟨65409386029712611466415767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43606257353141740977610511 65409386029712611466415767)
      ·
        refine ⟨98114079044568917199623651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65409386029712611466415767 98114079044568917199623651)
        ·
          refine ⟨147171118566853375799435477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98114079044568917199623651 147171118566853375799435477)
          ·
            refine ⟨3449323091410625995299269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 147171118566853375799435477 3449323091410625995299269)
            ·
              refine ⟨646748079639492374118613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3449323091410625995299269 646748079639492374118613)
              ·
                refine ⟨15158158116550602518405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 646748079639492374118613 15158158116550602518405)
                ·
                  rfl

theorem cell23_797051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 4, 7].length) (baseStart_797051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_797051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_797051 prefixEnd_797051 := by exact prefixLift 797051
  have htrace : WordTrace (prefixWord ++ tailWord_797051) baseStart_797051 baseEnd_797051 := by
    simpa [prefixWord, tailWord_797051, baseEnd_797051] using wordTrace_append hprefix tailTrace_797051
  have hstable : (prefixWord ++ tailWord_797051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797051).length < 2 ^ (prefixWord ++ tailWord_797051).sum := by decide
  have hdescent : baseEnd_797051 < baseStart_797051 := by decide
  rcases family_descends (prefixWord ++ tailWord_797051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797061 : List Nat := [1, 3, 1, 1, 3, 1, 1, 3, 3, 3, 3]
def baseStart_797061 : Nat := 118140960795 + 797061 * 2 ^ 59
def prefixEnd_797061 : Nat := 4983230072969 + 3 ^ 40 * 797061 * 2
def baseEnd_797061 : Nat := 409275403953411228871889

theorem tailTrace_797061 : CollatzResearch.WordTrace tailWord_797061 prefixEnd_797061 409275403953411228871889 := by
  unfold tailWord_797061
  simp only [CollatzResearch.WordTrace]
  refine ⟨29071202965391599026271037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19380801976927732684180691 29071202965391599026271037)
  ·
    refine ⟨10901701112021849634851639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29071202965391599026271037 10901701112021849634851639)
    ·
      refine ⟨16352551668032774452277459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10901701112021849634851639 16352551668032774452277459)
      ·
        refine ⟨24528827502049161678416189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16352551668032774452277459 24528827502049161678416189)
        ·
          refine ⟨9198310313268435629406071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24528827502049161678416189 9198310313268435629406071)
          ·
            refine ⟨13797465469902653444109107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9198310313268435629406071 13797465469902653444109107)
            ·
              refine ⟨20696198204853980166163661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13797465469902653444109107 20696198204853980166163661)
              ·
                refine ⟨7761074326820242562311373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20696198204853980166163661 7761074326820242562311373)
                ·
                  refine ⟨2910402872557590960866765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7761074326820242562311373 2910402872557590960866765)
                  ·
                    refine ⟨1091401077209096610325037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2910402872557590960866765 1091401077209096610325037)
                    ·
                      refine ⟨409275403953411228871889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1091401077209096610325037 409275403953411228871889)
                      ·
                        rfl

theorem cell23_797061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3, 3, 3].length) (baseStart_797061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_797061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_797061 prefixEnd_797061 := by exact prefixLift 797061
  have htrace : WordTrace (prefixWord ++ tailWord_797061) baseStart_797061 baseEnd_797061 := by
    simpa [prefixWord, tailWord_797061, baseEnd_797061] using wordTrace_append hprefix tailTrace_797061
  have hstable : (prefixWord ++ tailWord_797061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797061).length < 2 ^ (prefixWord ++ tailWord_797061).sum := by decide
  have hdescent : baseEnd_797061 < baseStart_797061 := by decide
  rcases family_descends (prefixWord ++ tailWord_797061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797089 : List Nat := [1, 2, 3, 5, 1, 2, 2, 1, 2, 4]
def baseStart_797089 : Nat := 118140960795 + 797089 * 2 ^ 59
def prefixEnd_797089 : Nat := 4983230072969 + 3 ^ 40 * 797089 * 2
def baseEnd_797089 : Nat := 136429927137245706440587

theorem tailTrace_797089 : CollatzResearch.WordTrace tailWord_797089 prefixEnd_797089 136429927137245706440587 := by
  unfold tailWord_797089
  simp only [CollatzResearch.WordTrace]
  refine ⟨29072224209290159808290321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19381482806193439872193547 29072224209290159808290321)
  ·
    refine ⟨21804168156967619856217741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29072224209290159808290321 21804168156967619856217741)
    ·
      refine ⟨8176563058862857446081653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21804168156967619856217741 8176563058862857446081653)
      ·
        refine ⟨766552786768392885570155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8176563058862857446081653 766552786768392885570155)
        ·
          refine ⟨1149829180152589328355233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 766552786768392885570155 1149829180152589328355233)
          ·
            refine ⟨862371885114441996266425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1149829180152589328355233 862371885114441996266425)
            ·
              refine ⟨646778913835831497199819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 862371885114441996266425 646778913835831497199819)
              ·
                refine ⟨970168370753747245799729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 646778913835831497199819 970168370753747245799729)
                ·
                  refine ⟨727626278065310434349797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 970168370753747245799729 727626278065310434349797)
                  ·
                    refine ⟨136429927137245706440587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 727626278065310434349797 136429927137245706440587)
                    ·
                      rfl

theorem cell23_797089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 2, 1, 2, 4].length) (baseStart_797089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_797089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_797089 prefixEnd_797089 := by exact prefixLift 797089
  have htrace : WordTrace (prefixWord ++ tailWord_797089) baseStart_797089 baseEnd_797089 := by
    simpa [prefixWord, tailWord_797089, baseEnd_797089] using wordTrace_append hprefix tailTrace_797089
  have hstable : (prefixWord ++ tailWord_797089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797089).length < 2 ^ (prefixWord ++ tailWord_797089).sum := by decide
  have hdescent : baseEnd_797089 < baseStart_797089 := by decide
  rcases family_descends (prefixWord ++ tailWord_797089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797105 : List Nat := [1, 2, 2, 4, 1, 3, 1, 1, 3, 3, 2]
def baseStart_797105 : Nat := 118140960795 + 797105 * 2 ^ 59
def prefixEnd_797105 : Nat := 4983230072969 + 3 ^ 40 * 797105 * 2
def baseEnd_797105 : Nat := 409297997102209056721687

theorem tailTrace_797105 : CollatzResearch.WordTrace tailWord_797105 prefixEnd_797105 409297997102209056721687 := by
  unfold tailWord_797105
  simp only [CollatzResearch.WordTrace]
  refine ⟨29072807777232194540872769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19381871851488129693915179 29072807777232194540872769)
  ·
    refine ⟨21804605832924145905654577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29072807777232194540872769 21804605832924145905654577)
    ·
      refine ⟨16353454374693109429240933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21804605832924145905654577 16353454374693109429240933)
      ·
        refine ⟨3066272695254958017982675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16353454374693109429240933 3066272695254958017982675)
        ·
          refine ⟨4599409042882437026974013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3066272695254958017982675 4599409042882437026974013)
          ·
            refine ⟨1724778391080913885115255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4599409042882437026974013 1724778391080913885115255)
            ·
              refine ⟨2587167586621370827672883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1724778391080913885115255 2587167586621370827672883)
              ·
                refine ⟨3880751379932056241509325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2587167586621370827672883 3880751379932056241509325)
                ·
                  refine ⟨1455281767474521090565997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3880751379932056241509325 1455281767474521090565997)
                  ·
                    refine ⟨545730662802945408962249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1455281767474521090565997 545730662802945408962249)
                    ·
                      refine ⟨409297997102209056721687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 545730662802945408962249 409297997102209056721687)
                      ·
                        rfl

theorem cell23_797105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_797105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_797105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_797105 prefixEnd_797105 := by exact prefixLift 797105
  have htrace : WordTrace (prefixWord ++ tailWord_797105) baseStart_797105 baseEnd_797105 := by
    simpa [prefixWord, tailWord_797105, baseEnd_797105] using wordTrace_append hprefix tailTrace_797105
  have hstable : (prefixWord ++ tailWord_797105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797105).length < 2 ^ (prefixWord ++ tailWord_797105).sum := by decide
  have hdescent : baseEnd_797105 < baseStart_797105 := by decide
  rcases family_descends (prefixWord ++ tailWord_797105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797131 : List Nat := [1, 1, 1, 1, 3, 3, 1, 4, 2, 2, 4]
def baseStart_797131 : Nat := 118140960795 + 797131 * 2 ^ 59
def prefixEnd_797131 : Nat := 4983230072969 + 3 ^ 40 * 797131 * 2
def baseEnd_797131 : Nat := 409311347599225954996567

theorem tailTrace_797131 : CollatzResearch.WordTrace tailWord_797131 prefixEnd_797131 409311347599225954996567 := by
  unfold tailWord_797131
  simp only [CollatzResearch.WordTrace]
  refine ⟨29073756075138000981319247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19382504050092000654212831 29073756075138000981319247)
  ·
    refine ⟨43610634112707001471978871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29073756075138000981319247 43610634112707001471978871)
    ·
      refine ⟨65415951169060502207968307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43610634112707001471978871 65415951169060502207968307)
      ·
        refine ⟨98123926753590753311952461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65415951169060502207968307 98123926753590753311952461)
        ·
          refine ⟨36796472532596532491982173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98123926753590753311952461 36796472532596532491982173)
          ·
            refine ⟨13798677199723699684493315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36796472532596532491982173 13798677199723699684493315)
            ·
              refine ⟨20698015799585549526739973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13798677199723699684493315 20698015799585549526739973)
              ·
                refine ⟨3880877962422290536263745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20698015799585549526739973 3880877962422290536263745)
                ·
                  refine ⟨2910658471816717902197809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3880877962422290536263745 2910658471816717902197809)
                  ·
                    refine ⟨2182993853862538426648357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2910658471816717902197809 2182993853862538426648357)
                    ·
                      refine ⟨409311347599225954996567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2182993853862538426648357 409311347599225954996567)
                      ·
                        rfl

theorem cell23_797131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 2, 2, 4].length) (baseStart_797131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_797131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_797131 prefixEnd_797131 := by exact prefixLift 797131
  have htrace : WordTrace (prefixWord ++ tailWord_797131) baseStart_797131 baseEnd_797131 := by
    simpa [prefixWord, tailWord_797131, baseEnd_797131] using wordTrace_append hprefix tailTrace_797131
  have hstable : (prefixWord ++ tailWord_797131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797131).length < 2 ^ (prefixWord ++ tailWord_797131).sum := by decide
  have hdescent : baseEnd_797131 < baseStart_797131 := by decide
  rcases family_descends (prefixWord ++ tailWord_797131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797171 : List Nat := [1, 1, 1, 2, 2, 2, 5, 1, 1, 7]
def baseStart_797171 : Nat := 118140960795 + 797171 * 2 ^ 59
def prefixEnd_797171 : Nat := 4983230072969 + 3 ^ 40 * 797171 * 2
def baseEnd_797171 : Nat := 136443962275135266165461

theorem tailTrace_797171 : CollatzResearch.WordTrace tailWord_797171 prefixEnd_797171 136443962275135266165461 := by
  unfold tailWord_797171
  simp only [CollatzResearch.WordTrace]
  refine ⟨29075214994993087812775367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19383476663328725208516911 29075214994993087812775367)
  ·
    refine ⟨43612822492489631719163051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29075214994993087812775367 43612822492489631719163051)
    ·
      refine ⟨65419233738734447578744577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43612822492489631719163051 65419233738734447578744577)
      ·
        refine ⟨49064425304050835684058433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65419233738734447578744577 49064425304050835684058433)
        ·
          refine ⟨36798318978038126763043825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49064425304050835684058433 36798318978038126763043825)
          ·
            refine ⟨27598739233528595072282869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36798318978038126763043825 27598739233528595072282869)
            ·
              refine ⟨2587381803143305788026519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27598739233528595072282869 2587381803143305788026519)
              ·
                refine ⟨3881072704714958682039779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2587381803143305788026519 3881072704714958682039779)
                ·
                  refine ⟨5821609057072438023059669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3881072704714958682039779 5821609057072438023059669)
                  ·
                    refine ⟨136443962275135266165461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5821609057072438023059669 136443962275135266165461)
                    ·
                      rfl

theorem cell23_797171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 7].length) (baseStart_797171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_797171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_797171 prefixEnd_797171 := by exact prefixLift 797171
  have htrace : WordTrace (prefixWord ++ tailWord_797171) baseStart_797171 baseEnd_797171 := by
    simpa [prefixWord, tailWord_797171, baseEnd_797171] using wordTrace_append hprefix tailTrace_797171
  have hstable : (prefixWord ++ tailWord_797171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797171).length < 2 ^ (prefixWord ++ tailWord_797171).sum := by decide
  have hdescent : baseEnd_797171 < baseStart_797171 := by decide
  rcases family_descends (prefixWord ++ tailWord_797171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797173 : List Nat := [1, 3, 5, 1, 3, 1, 2, 1, 1, 3, 2]
def baseStart_797173 : Nat := 118140960795 + 797173 * 2 ^ 59
def prefixEnd_797173 : Nat := 4983230072969 + 3 ^ 40 * 797173 * 2
def baseEnd_797173 : Nat := 409332913786714790671375

theorem tailTrace_797173 : CollatzResearch.WordTrace tailWord_797173 prefixEnd_797173 409332913786714790671375 := by
  unfold tailWord_797173
  simp only [CollatzResearch.WordTrace]
  refine ⟨29075287940985842154348173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19383525293990561436232115 29075287940985842154348173)
  ·
    refine ⟨10903232977869690807880565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29075287940985842154348173 10903232977869690807880565)
    ·
      refine ⟨1022178091675283513238803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10903232977869690807880565 1022178091675283513238803)
      ·
        refine ⟨1533267137512925269858205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1022178091675283513238803 1533267137512925269858205)
        ·
          refine ⟨574975176567346976196827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1533267137512925269858205 574975176567346976196827)
          ·
            refine ⟨862462764851020464295241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 574975176567346976196827 862462764851020464295241)
            ·
              refine ⟨646847073638265348221431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 862462764851020464295241 646847073638265348221431)
              ·
                refine ⟨970270610457398022332147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 646847073638265348221431 970270610457398022332147)
                ·
                  refine ⟨1455405915686097033498221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 970270610457398022332147 1455405915686097033498221)
                  ·
                    refine ⟨545777218382286387561833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1455405915686097033498221 545777218382286387561833)
                    ·
                      refine ⟨409332913786714790671375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 545777218382286387561833 409332913786714790671375)
                      ·
                        rfl

theorem cell23_797173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_797173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_797173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_797173 prefixEnd_797173 := by exact prefixLift 797173
  have htrace : WordTrace (prefixWord ++ tailWord_797173) baseStart_797173 baseEnd_797173 := by
    simpa [prefixWord, tailWord_797173, baseEnd_797173] using wordTrace_append hprefix tailTrace_797173
  have hstable : (prefixWord ++ tailWord_797173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797173).length < 2 ^ (prefixWord ++ tailWord_797173).sum := by decide
  have hdescent : baseEnd_797173 < baseStart_797173 := by decide
  rcases family_descends (prefixWord ++ tailWord_797173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797178 : List Nat := [3, 1, 1, 1, 1, 2, 2, 2, 1, 7, 2]
def baseStart_797178 : Nat := 118140960795 + 797178 * 2 ^ 59
def prefixEnd_797178 : Nat := 4983230072969 + 3 ^ 40 * 797178 * 2
def baseEnd_797178 : Nat := 409335481189987271108851

theorem tailTrace_797178 : CollatzResearch.WordTrace tailWord_797178 prefixEnd_797178 409335481189987271108851 := by
  unfold tailWord_797178
  simp only [CollatzResearch.WordTrace]
  refine ⟨7268867576491932002070047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19383646870645152005520125 7268867576491932002070047)
  ·
    refine ⟨10903301364737898003105071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7268867576491932002070047 10903301364737898003105071)
    ·
      refine ⟨16354952047106847004657607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10903301364737898003105071 16354952047106847004657607)
      ·
        refine ⟨24532428070660270506986411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16354952047106847004657607 24532428070660270506986411)
        ·
          refine ⟨36798642105990405760479617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24532428070660270506986411 36798642105990405760479617)
          ·
            refine ⟨27598981579492804320359713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36798642105990405760479617 27598981579492804320359713)
            ·
              refine ⟨20699236184619603240269785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27598981579492804320359713 20699236184619603240269785)
              ·
                refine ⟨15524427138464702430202339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20699236184619603240269785 15524427138464702430202339)
                ·
                  refine ⟨23286640707697053645303509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15524427138464702430202339 23286640707697053645303509)
                  ·
                    refine ⟨545780641586649694811801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23286640707697053645303509 545780641586649694811801)
                    ·
                      refine ⟨409335481189987271108851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 545780641586649694811801 409335481189987271108851)
                      ·
                        rfl

theorem cell23_797178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 1, 7, 2].length) (baseStart_797178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_797178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_797178 prefixEnd_797178 := by exact prefixLift 797178
  have htrace : WordTrace (prefixWord ++ tailWord_797178) baseStart_797178 baseEnd_797178 := by
    simpa [prefixWord, tailWord_797178, baseEnd_797178] using wordTrace_append hprefix tailTrace_797178
  have hstable : (prefixWord ++ tailWord_797178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797178).length < 2 ^ (prefixWord ++ tailWord_797178).sum := by decide
  have hdescent : baseEnd_797178 < baseStart_797178 := by decide
  rcases family_descends (prefixWord ++ tailWord_797178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797208 : List Nat := [2, 1, 2, 3, 3, 1, 1, 2, 1, 3, 4]
def baseStart_797208 : Nat := 118140960795 + 797208 * 2 ^ 59
def prefixEnd_797208 : Nat := 4983230072969 + 3 ^ 40 * 797208 * 2
def baseEnd_797208 : Nat := 409350885609622153733713

theorem tailTrace_797208 : CollatzResearch.WordTrace tailWord_797208 prefixEnd_797208 409350885609622153733713 := by
  unfold tailWord_797208
  simp only [CollatzResearch.WordTrace]
  refine ⟨14538282247929521565936139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19384376330572695421248185 14538282247929521565936139)
  ·
    refine ⟨21807423371894282348904209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14538282247929521565936139 21807423371894282348904209)
    ·
      refine ⟨16355567528920711761678157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21807423371894282348904209 16355567528920711761678157)
      ·
        refine ⟨6133337823345266910629309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16355567528920711761678157 6133337823345266910629309)
        ·
          refine ⟨2300001683754475091485991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6133337823345266910629309 2300001683754475091485991)
          ·
            refine ⟨3450002525631712637228987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2300001683754475091485991 3450002525631712637228987)
            ·
              refine ⟨5175003788447568955843481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3450002525631712637228987 5175003788447568955843481)
              ·
                refine ⟨3881252841335676716882611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5175003788447568955843481 3881252841335676716882611)
                ·
                  refine ⟨5821879262003515075323917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3881252841335676716882611 5821879262003515075323917)
                  ·
                    refine ⟨2183204723251318153246469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5821879262003515075323917 2183204723251318153246469)
                    ·
                      refine ⟨409350885609622153733713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2183204723251318153246469 409350885609622153733713)
                      ·
                        rfl

theorem cell23_797208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_797208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_797208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_797208 prefixEnd_797208 := by exact prefixLift 797208
  have htrace : WordTrace (prefixWord ++ tailWord_797208) baseStart_797208 baseEnd_797208 := by
    simpa [prefixWord, tailWord_797208, baseEnd_797208] using wordTrace_append hprefix tailTrace_797208
  have hstable : (prefixWord ++ tailWord_797208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797208).length < 2 ^ (prefixWord ++ tailWord_797208).sum := by decide
  have hdescent : baseEnd_797208 < baseStart_797208 := by decide
  rcases family_descends (prefixWord ++ tailWord_797208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797228 : List Nat := [2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 3]
def baseStart_797228 : Nat := 118140960795 + 797228 * 2 ^ 59
def prefixEnd_797228 : Nat := 4983230072969 + 3 ^ 40 * 797228 * 2
def baseEnd_797228 : Nat := 409361155222712075483621

theorem tailTrace_797228 : CollatzResearch.WordTrace tailWord_797228 prefixEnd_797228 409361155222712075483621 := by
  unfold tailWord_797228
  simp only [CollatzResearch.WordTrace]
  refine ⟨14538646977893293273800169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19384862637191057698400225 14538646977893293273800169)
  ·
    refine ⟨10903985233419969955350127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14538646977893293273800169 10903985233419969955350127)
    ·
      refine ⟨16355977850129954933025191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10903985233419969955350127 16355977850129954933025191)
      ·
        refine ⟨24533966775194932399537787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16355977850129954933025191 24533966775194932399537787)
        ·
          refine ⟨36800950162792398599306681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24533966775194932399537787 36800950162792398599306681)
          ·
            refine ⟨27600712622094298949480011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36800950162792398599306681 27600712622094298949480011)
            ·
              refine ⟨41401068933141448424220017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27600712622094298949480011 41401068933141448424220017)
              ·
                refine ⟨31050801699856086318165013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41401068933141448424220017 31050801699856086318165013)
                ·
                  refine ⟨1455506329680754046163985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 31050801699856086318165013 1455506329680754046163985)
                  ·
                    refine ⟨1091629747260565534622989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1455506329680754046163985 1091629747260565534622989)
                    ·
                      refine ⟨409361155222712075483621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1091629747260565534622989 409361155222712075483621)
                      ·
                        rfl

theorem cell23_797228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 3].length) (baseStart_797228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_797228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_797228 prefixEnd_797228 := by exact prefixLift 797228
  have htrace : WordTrace (prefixWord ++ tailWord_797228) baseStart_797228 baseEnd_797228 := by
    simpa [prefixWord, tailWord_797228, baseEnd_797228] using wordTrace_append hprefix tailTrace_797228
  have hstable : (prefixWord ++ tailWord_797228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797228).length < 2 ^ (prefixWord ++ tailWord_797228).sum := by decide
  have hdescent : baseEnd_797228 < baseStart_797228 := by decide
  rcases family_descends (prefixWord ++ tailWord_797228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797245 : List Nat := [1, 4, 1, 3, 2, 1, 1, 1, 4, 2, 3]
def baseStart_797245 : Nat := 118140960795 + 797245 * 2 ^ 59
def prefixEnd_797245 : Nat := 4983230072969 + 3 ^ 40 * 797245 * 2
def baseEnd_797245 : Nat := 409369884393838508971043

theorem tailTrace_797245 : CollatzResearch.WordTrace tailWord_797245 prefixEnd_797245 409369884393838508971043 := by
  unfold tailWord_797245
  simp only [CollatzResearch.WordTrace]
  refine ⟨29077913996724998450969189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19385275997816665633979459 29077913996724998450969189)
  ·
    refine ⟨5452108874385937209556723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29077913996724998450969189 5452108874385937209556723)
    ·
      refine ⟨8178163311578905814335085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5452108874385937209556723 8178163311578905814335085)
      ·
        refine ⟨3066811241842089680375657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8178163311578905814335085 3066811241842089680375657)
        ·
          refine ⟨2300108431381567260281743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3066811241842089680375657 2300108431381567260281743)
          ·
            refine ⟨3450162647072350890422615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2300108431381567260281743 3450162647072350890422615)
            ·
              refine ⟨5175243970608526335633923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3450162647072350890422615 5175243970608526335633923)
              ·
                refine ⟨7762865955912789503450885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5175243970608526335633923 7762865955912789503450885)
                ·
                  refine ⟨1455537366733648031897041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7762865955912789503450885 1455537366733648031897041)
                  ·
                    refine ⟨1091653025050236023922781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1455537366733648031897041 1091653025050236023922781)
                    ·
                      refine ⟨409369884393838508971043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1091653025050236023922781 409369884393838508971043)
                      ·
                        rfl

theorem cell23_797245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_797245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_797245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_797245 prefixEnd_797245 := by exact prefixLift 797245
  have htrace : WordTrace (prefixWord ++ tailWord_797245) baseStart_797245 baseEnd_797245 := by
    simpa [prefixWord, tailWord_797245, baseEnd_797245] using wordTrace_append hprefix tailTrace_797245
  have hstable : (prefixWord ++ tailWord_797245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797245).length < 2 ^ (prefixWord ++ tailWord_797245).sum := by decide
  have hdescent : baseEnd_797245 < baseStart_797245 := by decide
  rcases family_descends (prefixWord ++ tailWord_797245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797251 : List Nat := [1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 8]
def baseStart_797251 : Nat := 118140960795 + 797251 * 2 ^ 59
def prefixEnd_797251 : Nat := 4983230072969 + 3 ^ 40 * 797251 * 2
def baseEnd_797251 : Nat := 409372965277765485496015

theorem tailTrace_797251 : CollatzResearch.WordTrace tailWord_797251 prefixEnd_797251 409372965277765485496015 := by
  unfold tailWord_797251
  simp only [CollatzResearch.WordTrace]
  refine ⟨29078132834703261475687607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19385421889802174317125071 29078132834703261475687607)
  ·
    refine ⟨43617199252054892213531411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29078132834703261475687607 43617199252054892213531411)
    ·
      refine ⟨65425798878082338320297117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43617199252054892213531411 65425798878082338320297117)
      ·
        refine ⟨24534674579280876870111419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65425798878082338320297117 24534674579280876870111419)
        ·
          refine ⟨36802011868921315305167129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24534674579280876870111419 36802011868921315305167129)
          ·
            refine ⟨27601508901690986478875347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36802011868921315305167129 27601508901690986478875347)
            ·
              refine ⟨41402263352536479718313021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27601508901690986478875347 41402263352536479718313021)
              ·
                refine ⟨15525848757201179894367383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41402263352536479718313021 15525848757201179894367383)
                ·
                  refine ⟨23288773135801769841551075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15525848757201179894367383 23288773135801769841551075)
                  ·
                    refine ⟨34933159703702654762326613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23288773135801769841551075 34933159703702654762326613)
                    ·
                      refine ⟨409372965277765485496015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 34933159703702654762326613 409372965277765485496015)
                      ·
                        rfl

theorem cell23_797251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 8].length) (baseStart_797251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_797251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_797251 prefixEnd_797251 := by exact prefixLift 797251
  have htrace : WordTrace (prefixWord ++ tailWord_797251) baseStart_797251 baseEnd_797251 := by
    simpa [prefixWord, tailWord_797251, baseEnd_797251] using wordTrace_append hprefix tailTrace_797251
  have hstable : (prefixWord ++ tailWord_797251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797251).length < 2 ^ (prefixWord ++ tailWord_797251).sum := by decide
  have hdescent : baseEnd_797251 < baseStart_797251 := by decide
  rcases family_descends (prefixWord ++ tailWord_797251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797265 : List Nat := [1, 2, 2, 1, 3, 3, 4, 1, 6]
def baseStart_797265 : Nat := 118140960795 + 797265 * 2 ^ 59
def prefixEnd_797265 : Nat := 4983230072969 + 3 ^ 40 * 797265 * 2
def baseEnd_797265 : Nat := 45486683778547603413439

theorem tailTrace_797265 : CollatzResearch.WordTrace tailWord_797265 prefixEnd_797265 45486683778547603413439 := by
  unfold tailWord_797265
  simp only [CollatzResearch.WordTrace]
  refine ⟨29078643456652541866697249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19385762304435027911131499 29078643456652541866697249)
  ·
    refine ⟨21808982592489406400022937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29078643456652541866697249 21808982592489406400022937)
    ·
      refine ⟨16356736944367054800017203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21808982592489406400022937 16356736944367054800017203)
      ·
        refine ⟨24535105416550582200025805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16356736944367054800017203 24535105416550582200025805)
        ·
          refine ⟨9200664531206468325009677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24535105416550582200025805 9200664531206468325009677)
          ·
            refine ⟨3450249199202425621878629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9200664531206468325009677 3450249199202425621878629)
            ·
              refine ⟨646921724850454804102243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3450249199202425621878629 646921724850454804102243)
              ·
                refine ⟨970382587275682206153365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 646921724850454804102243 970382587275682206153365)
                ·
                  refine ⟨45486683778547603413439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 970382587275682206153365 45486683778547603413439)
                  ·
                    rfl

theorem cell23_797265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 4, 1, 6].length) (baseStart_797265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_797265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_797265 prefixEnd_797265 := by exact prefixLift 797265
  have htrace : WordTrace (prefixWord ++ tailWord_797265) baseStart_797265 baseEnd_797265 := by
    simpa [prefixWord, tailWord_797265, baseEnd_797265] using wordTrace_append hprefix tailTrace_797265
  have hstable : (prefixWord ++ tailWord_797265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797265).length < 2 ^ (prefixWord ++ tailWord_797265).sum := by decide
  have hdescent : baseEnd_797265 < baseStart_797265 := by decide
  rcases family_descends (prefixWord ++ tailWord_797265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797332 : List Nat := [2, 4, 2, 2, 1, 1, 2, 1, 3, 1, 4]
def baseStart_797332 : Nat := 118140960795 + 797332 * 2 ^ 59
def prefixEnd_797332 : Nat := 4983230072969 + 3 ^ 40 * 797332 * 2
def baseEnd_797332 : Nat := 409414557210779668583143

theorem tailTrace_797332 : CollatzResearch.WordTrace tailWord_797332 prefixEnd_797332 409414557210779668583143 := by
  unfold tailWord_797332
  simp only [CollatzResearch.WordTrace]
  refine ⟨14540543573704906154693125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19387391431606541539590833 14540543573704906154693125)
  ·
    refine ⟨2726351920069669904004961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14540543573704906154693125 2726351920069669904004961)
    ·
      refine ⟨2044763940052252428003721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2726351920069669904004961 2044763940052252428003721)
      ·
        refine ⟨1533572955039189321002791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2044763940052252428003721 1533572955039189321002791)
        ·
          refine ⟨2300359432558783981504187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1533572955039189321002791 2300359432558783981504187)
          ·
            refine ⟨3450539148838175972256281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2300359432558783981504187 3450539148838175972256281)
            ·
              refine ⟨2587904361628631979192211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3450539148838175972256281 2587904361628631979192211)
              ·
                refine ⟨3881856542442947968788317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2587904361628631979192211 3881856542442947968788317)
                ·
                  refine ⟨1455696203416105488295619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3881856542442947968788317 1455696203416105488295619)
                  ·
                    refine ⟨2183544305124158232443429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1455696203416105488295619 2183544305124158232443429)
                    ·
                      refine ⟨409414557210779668583143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2183544305124158232443429 409414557210779668583143)
                      ·
                        rfl

theorem cell23_797332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_797332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_797332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_797332 prefixEnd_797332 := by exact prefixLift 797332
  have htrace : WordTrace (prefixWord ++ tailWord_797332) baseStart_797332 baseEnd_797332 := by
    simpa [prefixWord, tailWord_797332, baseEnd_797332] using wordTrace_append hprefix tailTrace_797332
  have hstable : (prefixWord ++ tailWord_797332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797332).length < 2 ^ (prefixWord ++ tailWord_797332).sum := by decide
  have hdescent : baseEnd_797332 < baseStart_797332 := by decide
  rcases family_descends (prefixWord ++ tailWord_797332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797335 : List Nat := [1, 1, 3, 3, 2, 1, 1, 3, 3, 2, 3]
def baseStart_797335 : Nat := 118140960795 + 797335 * 2 ^ 59
def prefixEnd_797335 : Nat := 4983230072969 + 3 ^ 40 * 797335 * 2
def baseEnd_797335 : Nat := 409416097652743156845629

theorem tailTrace_797335 : CollatzResearch.WordTrace tailWord_797335 prefixEnd_797335 409416097652743156845629 := by
  unfold tailWord_797335
  simp only [CollatzResearch.WordTrace]
  refine ⟨29081196566398943821745459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19387464377599295881163639 29081196566398943821745459)
  ·
    refine ⟨43621794849598415732618189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29081196566398943821745459 43621794849598415732618189)
    ·
      refine ⟨16358173068599405899731821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43621794849598415732618189 16358173068599405899731821)
      ·
        refine ⟨6134314900724777212399433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16358173068599405899731821 6134314900724777212399433)
        ·
          refine ⟨4600736175543582909299575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6134314900724777212399433 4600736175543582909299575)
          ·
            refine ⟨6901104263315374363949363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4600736175543582909299575 6901104263315374363949363)
            ·
              refine ⟨10351656394973061545924045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6901104263315374363949363 10351656394973061545924045)
              ·
                refine ⟨3881871148114898079721517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10351656394973061545924045 3881871148114898079721517)
                ·
                  refine ⟨1455701680543086779895569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3881871148114898079721517 1455701680543086779895569)
                  ·
                    refine ⟨1091776260407315084921677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1455701680543086779895569 1091776260407315084921677)
                    ·
                      refine ⟨409416097652743156845629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1091776260407315084921677 409416097652743156845629)
                      ·
                        rfl

theorem cell23_797335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_797335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_797335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_797335 prefixEnd_797335 := by exact prefixLift 797335
  have htrace : WordTrace (prefixWord ++ tailWord_797335) baseStart_797335 baseEnd_797335 := by
    simpa [prefixWord, tailWord_797335, baseEnd_797335] using wordTrace_append hprefix tailTrace_797335
  have hstable : (prefixWord ++ tailWord_797335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797335).length < 2 ^ (prefixWord ++ tailWord_797335).sum := by decide
  have hdescent : baseEnd_797335 < baseStart_797335 := by decide
  rcases family_descends (prefixWord ++ tailWord_797335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797342 : List Nat := [4, 3, 1, 1, 1, 1, 2, 2, 4, 4]
def baseStart_797342 : Nat := 118140960795 + 797342 * 2 ^ 59
def prefixEnd_797342 : Nat := 4983230072969 + 3 ^ 40 * 797342 * 2
def baseEnd_797342 : Nat := 136473230672441543152699

theorem tailTrace_797342 : CollatzResearch.WordTrace tailWord_797342 prefixEnd_797342 136473230672441543152699 := by
  unfold tailWord_797342
  simp only [CollatzResearch.WordTrace]
  refine ⟨3635181484671698002156285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19387634584915722678166853 3635181484671698002156285)
  ·
    refine ⟨1363193056751886750808607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3635181484671698002156285 1363193056751886750808607)
    ·
      refine ⟨2044789585127830126212911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1363193056751886750808607 2044789585127830126212911)
      ·
        refine ⟨3067184377691745189319367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2044789585127830126212911 3067184377691745189319367)
        ·
          refine ⟨4600776566537617783979051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3067184377691745189319367 4600776566537617783979051)
          ·
            refine ⟨6901164849806426675968577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4600776566537617783979051 6901164849806426675968577)
            ·
              refine ⟨5175873637354820006976433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6901164849806426675968577 5175873637354820006976433)
              ·
                refine ⟨3881905228016115005232325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5175873637354820006976433 3881905228016115005232325)
                ·
                  refine ⟨727857230253021563481061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3881905228016115005232325 727857230253021563481061)
                  ·
                    refine ⟨136473230672441543152699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 727857230253021563481061 136473230672441543152699)
                    ·
                      rfl

theorem cell23_797342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_797342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_797342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_797342 prefixEnd_797342 := by exact prefixLift 797342
  have htrace : WordTrace (prefixWord ++ tailWord_797342) baseStart_797342 baseEnd_797342 := by
    simpa [prefixWord, tailWord_797342, baseEnd_797342] using wordTrace_append hprefix tailTrace_797342
  have hstable : (prefixWord ++ tailWord_797342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797342).length < 2 ^ (prefixWord ++ tailWord_797342).sum := by decide
  have hdescent : baseEnd_797342 < baseStart_797342 := by decide
  rcases family_descends (prefixWord ++ tailWord_797342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797409 : List Nat := [1, 2, 3, 1, 4, 1, 2, 3, 1, 3, 2]
def baseStart_797409 : Nat := 118140960795 + 797409 * 2 ^ 59
def prefixEnd_797409 : Nat := 4983230072969 + 3 ^ 40 * 797409 * 2
def baseEnd_797409 : Nat := 409454095221175867320289

theorem tailTrace_797409 : CollatzResearch.WordTrace tailWord_797409 prefixEnd_797409 409454095221175867320289 := by
  unfold tailWord_797409
  simp only [CollatzResearch.WordTrace]
  refine ⟨29083895568130854459939281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19389263712087236306626187 29083895568130854459939281)
  ·
    refine ⟨21812921676098140844954461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29083895568130854459939281 21812921676098140844954461)
    ·
      refine ⟨8179845628536802816857923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21812921676098140844954461 8179845628536802816857923)
      ·
        refine ⟨12269768442805204225286885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8179845628536802816857923 12269768442805204225286885)
        ·
          refine ⟨2300581583025975792241291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12269768442805204225286885 2300581583025975792241291)
          ·
            refine ⟨3450872374538963688361937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2300581583025975792241291 3450872374538963688361937)
            ·
              refine ⟨2588154280904222766271453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3450872374538963688361937 2588154280904222766271453)
              ·
                refine ⟨970557855339083537351795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2588154280904222766271453 970557855339083537351795)
                ·
                  refine ⟨1455836783008625306027693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 970557855339083537351795 1455836783008625306027693)
                  ·
                    refine ⟨545938793628234489760385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1455836783008625306027693 545938793628234489760385)
                    ·
                      refine ⟨409454095221175867320289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 545938793628234489760385 409454095221175867320289)
                      ·
                        rfl

theorem cell23_797409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 3, 1, 3, 2].length) (baseStart_797409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_797409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_797409 prefixEnd_797409 := by exact prefixLift 797409
  have htrace : WordTrace (prefixWord ++ tailWord_797409) baseStart_797409 baseEnd_797409 := by
    simpa [prefixWord, tailWord_797409, baseEnd_797409] using wordTrace_append hprefix tailTrace_797409
  have hstable : (prefixWord ++ tailWord_797409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797409).length < 2 ^ (prefixWord ++ tailWord_797409).sum := by decide
  have hdescent : baseEnd_797409 < baseStart_797409 := by decide
  rcases family_descends (prefixWord ++ tailWord_797409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797425 : List Nat := [1, 2, 2, 2, 2, 2, 2, 1, 2, 4, 3]
def baseStart_797425 : Nat := 118140960795 + 797425 * 2 ^ 59
def prefixEnd_797425 : Nat := 4983230072969 + 3 ^ 40 * 797425 * 2
def baseEnd_797425 : Nat := 409462310911647804720215

theorem tailTrace_797425 : CollatzResearch.WordTrace tailWord_797425 prefixEnd_797425 409462310911647804720215 := by
  unfold tailWord_797425
  simp only [CollatzResearch.WordTrace]
  refine ⟨29084479136072889192521729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19389652757381926128347819 29084479136072889192521729)
  ·
    refine ⟨21813359352054666894391297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29084479136072889192521729 21813359352054666894391297)
    ·
      refine ⟨16360019514041000170793473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21813359352054666894391297 16360019514041000170793473)
      ·
        refine ⟨12270014635530750128095105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16360019514041000170793473 12270014635530750128095105)
        ·
          refine ⟨9202510976648062596071329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12270014635530750128095105 9202510976648062596071329)
          ·
            refine ⟨6901883232486046947053497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9202510976648062596071329 6901883232486046947053497)
            ·
              refine ⟨5176412424364535210290123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6901883232486046947053497 5176412424364535210290123)
              ·
                refine ⟨7764618636546802815435185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5176412424364535210290123 7764618636546802815435185)
                ·
                  refine ⟨5823463977410102111576389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7764618636546802815435185 5823463977410102111576389)
                  ·
                    refine ⟨1091899495764394145920573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5823463977410102111576389 1091899495764394145920573)
                    ·
                      refine ⟨409462310911647804720215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1091899495764394145920573 409462310911647804720215)
                      ·
                        rfl

theorem cell23_797425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 4, 3].length) (baseStart_797425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_797425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_797425 prefixEnd_797425 := by exact prefixLift 797425
  have htrace : WordTrace (prefixWord ++ tailWord_797425) baseStart_797425 baseEnd_797425 := by
    simpa [prefixWord, tailWord_797425, baseEnd_797425] using wordTrace_append hprefix tailTrace_797425
  have hstable : (prefixWord ++ tailWord_797425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797425).length < 2 ^ (prefixWord ++ tailWord_797425).sum := by decide
  have hdescent : baseEnd_797425 < baseStart_797425 := by decide
  rcases family_descends (prefixWord ++ tailWord_797425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797442 : List Nat := [3, 4, 1, 1, 1, 2, 1, 2, 2, 1, 5]
def baseStart_797442 : Nat := 118140960795 + 797442 * 2 ^ 59
def prefixEnd_797442 : Nat := 4983230072969 + 3 ^ 40 * 797442 * 2
def baseEnd_797442 : Nat := 409471040082774238207637

theorem tailTrace_797442 : CollatzResearch.WordTrace tailWord_797442 prefixEnd_797442 409471040082774238207637 := by
  unfold tailWord_797442
  simp only [CollatzResearch.WordTrace]
  refine ⟨7271274794252825273972645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19390066118007534063927053 7271274794252825273972645)
  ·
    refine ⟨1363364023922404738869871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7271274794252825273972645 1363364023922404738869871)
    ·
      refine ⟨2045046035883607108304807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1363364023922404738869871 2045046035883607108304807)
      ·
        refine ⟨3067569053825410662457211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2045046035883607108304807 3067569053825410662457211)
        ·
          refine ⟨4601353580738115993685817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3067569053825410662457211 4601353580738115993685817)
          ·
            refine ⟨3451015185553586995264363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4601353580738115993685817 3451015185553586995264363)
            ·
              refine ⟨5176522778330380492896545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3451015185553586995264363 5176522778330380492896545)
              ·
                refine ⟨3882392083747785369672409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5176522778330380492896545 3882392083747785369672409)
                ·
                  refine ⟨2911794062810839027254307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3882392083747785369672409 2911794062810839027254307)
                  ·
                    refine ⟨4367691094216258540881461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2911794062810839027254307 4367691094216258540881461)
                    ·
                      refine ⟨409471040082774238207637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4367691094216258540881461 409471040082774238207637)
                      ·
                        rfl

theorem cell23_797442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_797442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_797442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_797442 prefixEnd_797442 := by exact prefixLift 797442
  have htrace : WordTrace (prefixWord ++ tailWord_797442) baseStart_797442 baseEnd_797442 := by
    simpa [prefixWord, tailWord_797442, baseEnd_797442] using wordTrace_append hprefix tailTrace_797442
  have hstable : (prefixWord ++ tailWord_797442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797442).length < 2 ^ (prefixWord ++ tailWord_797442).sum := by decide
  have hdescent : baseEnd_797442 < baseStart_797442 := by decide
  rcases family_descends (prefixWord ++ tailWord_797442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797495 : List Nat := [1, 1, 3, 1, 2, 1, 4, 2, 1, 3, 4]
def baseStart_797495 : Nat := 118140960795 + 797495 * 2 ^ 59
def prefixEnd_797495 : Nat := 4983230072969 + 3 ^ 40 * 797495 * 2
def baseEnd_797495 : Nat := 409498254557462530844893

theorem tailTrace_797495 : CollatzResearch.WordTrace tailWord_797495 prefixEnd_797495 409498254557462530844893 := by
  unfold tailWord_797495
  simp only [CollatzResearch.WordTrace]
  refine ⟨29087032245819291147569939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19391354830546194098379959 29087032245819291147569939)
  ·
    refine ⟨43630548368728936721354909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29087032245819291147569939 43630548368728936721354909)
    ·
      refine ⟨16361455638273351270508091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43630548368728936721354909 16361455638273351270508091)
      ·
        refine ⟨24542183457410026905762137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16361455638273351270508091 24542183457410026905762137)
        ·
          refine ⟨18406637593057520179321603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24542183457410026905762137 18406637593057520179321603)
          ·
            refine ⟨27609956389586280268982405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18406637593057520179321603 27609956389586280268982405)
            ·
              refine ⟨5176866823047427550434201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27609956389586280268982405 5176866823047427550434201)
              ·
                refine ⟨3882650117285570662825651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5176866823047427550434201 3882650117285570662825651)
                ·
                  refine ⟨5823975175928355994238477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3882650117285570662825651 5823975175928355994238477)
                  ·
                    refine ⟨2183990690973133497839429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5823975175928355994238477 2183990690973133497839429)
                    ·
                      refine ⟨409498254557462530844893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2183990690973133497839429 409498254557462530844893)
                      ·
                        rfl

theorem cell23_797495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 3, 4].length) (baseStart_797495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_797495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_797495 prefixEnd_797495 := by exact prefixLift 797495
  have htrace : WordTrace (prefixWord ++ tailWord_797495) baseStart_797495 baseEnd_797495 := by
    simpa [prefixWord, tailWord_797495, baseEnd_797495] using wordTrace_append hprefix tailTrace_797495
  have hstable : (prefixWord ++ tailWord_797495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797495).length < 2 ^ (prefixWord ++ tailWord_797495).sum := by decide
  have hdescent : baseEnd_797495 < baseStart_797495 := by decide
  rcases family_descends (prefixWord ++ tailWord_797495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797512 : List Nat := [2, 1, 3, 1, 1, 3, 1, 2, 1, 6, 2]
def baseStart_797512 : Nat := 118140960795 + 797512 * 2 ^ 59
def prefixEnd_797512 : Nat := 4983230072969 + 3 ^ 40 * 797512 * 2
def baseEnd_797512 : Nat := 409506983728588964332315

theorem tailTrace_797512 : CollatzResearch.WordTrace tailWord_797512 prefixEnd_797512 409506983728588964332315 := by
  unfold tailWord_797512
  simp only [CollatzResearch.WordTrace]
  refine ⟨14543826143378851525469395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19391768191171802033959193 14543826143378851525469395)
  ·
    refine ⟨21815739215068277288204093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14543826143378851525469395 21815739215068277288204093)
    ·
      refine ⟨8180902205650603983076535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21815739215068277288204093 8180902205650603983076535)
      ·
        refine ⟨12271353308475905974614803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8180902205650603983076535 12271353308475905974614803)
        ·
          refine ⟨18407029962713858961922205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12271353308475905974614803 18407029962713858961922205)
          ·
            refine ⟨6902636236017697110720827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18407029962713858961922205 6902636236017697110720827)
            ·
              refine ⟨10353954354026545666081241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6902636236017697110720827 10353954354026545666081241)
              ·
                refine ⟨7765465765519909249560931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10353954354026545666081241 7765465765519909249560931)
                ·
                  refine ⟨11648198648279863874341397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7765465765519909249560931 11648198648279863874341397)
                  ·
                    refine ⟨546009311638118619109753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11648198648279863874341397 546009311638118619109753)
                    ·
                      refine ⟨409506983728588964332315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 546009311638118619109753 409506983728588964332315)
                      ·
                        rfl

theorem cell23_797512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 1, 6, 2].length) (baseStart_797512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_797512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_797512 prefixEnd_797512 := by exact prefixLift 797512
  have htrace : WordTrace (prefixWord ++ tailWord_797512) baseStart_797512 baseEnd_797512 := by
    simpa [prefixWord, tailWord_797512, baseEnd_797512] using wordTrace_append hprefix tailTrace_797512
  have hstable : (prefixWord ++ tailWord_797512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797512).length < 2 ^ (prefixWord ++ tailWord_797512).sum := by decide
  have hdescent : baseEnd_797512 < baseStart_797512 := by decide
  rcases family_descends (prefixWord ++ tailWord_797512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797522 : List Nat := [3, 2, 2, 1, 1, 2, 1, 2, 5, 4]
def baseStart_797522 : Nat := 118140960795 + 797522 * 2 ^ 59
def prefixEnd_797522 : Nat := 4983230072969 + 3 ^ 40 * 797522 * 2
def baseEnd_797522 : Nat := 136504039511711308402423

theorem tailTrace_797522 : CollatzResearch.WordTrace tailWord_797522 prefixEnd_797522 136504039511711308402423 := by
  unfold tailWord_797522
  simp only [CollatzResearch.WordTrace]
  refine ⟨7272004254180368689700705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19392011344480983172535213 7272004254180368689700705)
  ·
    refine ⟨5454003190635276517275529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7272004254180368689700705 5454003190635276517275529)
    ·
      refine ⟨4090502392976457387956647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5454003190635276517275529 4090502392976457387956647)
      ·
        refine ⟨6135753589464686081934971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4090502392976457387956647 6135753589464686081934971)
        ·
          refine ⟨9203630384197029122902457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6135753589464686081934971 9203630384197029122902457)
          ·
            refine ⟨6902722788147771842176843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9203630384197029122902457 6902722788147771842176843)
            ·
              refine ⟨10354084182221657763265265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6902722788147771842176843 10354084182221657763265265)
              ·
                refine ⟨7765563136666243322448949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10354084182221657763265265 7765563136666243322448949)
                ·
                  refine ⟨728021544062460311479589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7765563136666243322448949 728021544062460311479589)
                  ·
                    refine ⟨136504039511711308402423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 728021544062460311479589 136504039511711308402423)
                    ·
                      rfl

theorem cell23_797522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_797522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_797522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_797522 prefixEnd_797522 := by exact prefixLift 797522
  have htrace : WordTrace (prefixWord ++ tailWord_797522) baseStart_797522 baseEnd_797522 := by
    simpa [prefixWord, tailWord_797522, baseEnd_797522] using wordTrace_append hprefix tailTrace_797522
  have hstable : (prefixWord ++ tailWord_797522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797522).length < 2 ^ (prefixWord ++ tailWord_797522).sum := by decide
  have hdescent : baseEnd_797522 < baseStart_797522 := by decide
  rcases family_descends (prefixWord ++ tailWord_797522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797525 : List Nat := [1, 3, 2, 2, 2, 1, 1, 1, 1, 3, 6]
def baseStart_797525 : Nat := 118140960795 + 797525 * 2 ^ 59
def prefixEnd_797525 : Nat := 4983230072969 + 3 ^ 40 * 797525 * 2
def baseEnd_797525 : Nat := 409513658977097413469755

theorem tailTrace_797525 : CollatzResearch.WordTrace tailWord_797525 prefixEnd_797525 409513658977097413469755 := by
  unfold tailWord_797525
  simp only [CollatzResearch.WordTrace]
  refine ⟨29088126435710606271162029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19392084290473737514108019 29088126435710606271162029)
  ·
    refine ⟨10908047413391477351685761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29088126435710606271162029 10908047413391477351685761)
    ·
      refine ⟨8181035560043608013764321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10908047413391477351685761 8181035560043608013764321)
      ·
        refine ⟨6135776670032706010323241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8181035560043608013764321 6135776670032706010323241)
        ·
          refine ⟨4601832502524529507742431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6135776670032706010323241 4601832502524529507742431)
          ·
            refine ⟨6902748753786794261613647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4601832502524529507742431 6902748753786794261613647)
            ·
              refine ⟨10354123130680191392420471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6902748753786794261613647 10354123130680191392420471)
              ·
                refine ⟨15531184696020287088630707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10354123130680191392420471 15531184696020287088630707)
                ·
                  refine ⟨23296777044030430632946061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15531184696020287088630707 23296777044030430632946061)
                  ·
                    refine ⟨8736291391511411487354773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23296777044030430632946061 8736291391511411487354773)
                    ·
                      refine ⟨409513658977097413469755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8736291391511411487354773 409513658977097413469755)
                      ·
                        rfl

theorem cell23_797525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_797525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_797525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_797525 prefixEnd_797525 := by exact prefixLift 797525
  have htrace : WordTrace (prefixWord ++ tailWord_797525) baseStart_797525 baseEnd_797525 := by
    simpa [prefixWord, tailWord_797525, baseEnd_797525] using wordTrace_append hprefix tailTrace_797525
  have hstable : (prefixWord ++ tailWord_797525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797525).length < 2 ^ (prefixWord ++ tailWord_797525).sum := by decide
  have hdescent : baseEnd_797525 < baseStart_797525 := by decide
  rcases family_descends (prefixWord ++ tailWord_797525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797535 : List Nat := [1, 1, 2, 3, 1, 3, 3, 1, 8]
def baseStart_797535 : Nat := 118140960795 + 797535 * 2 ^ 59
def prefixEnd_797535 : Nat := 4983230072969 + 3 ^ 40 * 797535 * 2
def baseEnd_797535 : Nat := 45502088198182486038301

theorem tailTrace_797535 : CollatzResearch.WordTrace tailWord_797535 prefixEnd_797535 45502088198182486038301 := by
  unfold tailWord_797535
  simp only [CollatzResearch.WordTrace]
  refine ⟨29088491165674377979026059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19392327443782918652684039 29088491165674377979026059)
  ·
    refine ⟨43632736748511566968539089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29088491165674377979026059 43632736748511566968539089)
    ·
      refine ⟨32724552561383675226404317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43632736748511566968539089 32724552561383675226404317)
      ·
        refine ⟨12271707210518878209901619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32724552561383675226404317 12271707210518878209901619)
        ·
          refine ⟨18407560815778317314852429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12271707210518878209901619 18407560815778317314852429)
          ·
            refine ⟨6902835305916868993069661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18407560815778317314852429 6902835305916868993069661)
            ·
              refine ⟨2588563239718825872401123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6902835305916868993069661 2588563239718825872401123)
              ·
                refine ⟨3882844859578238808601685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2588563239718825872401123 3882844859578238808601685)
                ·
                  refine ⟨45502088198182486038301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3882844859578238808601685 45502088198182486038301)
                  ·
                    rfl

theorem cell23_797535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 8].length) (baseStart_797535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_797535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_797535 prefixEnd_797535 := by exact prefixLift 797535
  have htrace : WordTrace (prefixWord ++ tailWord_797535) baseStart_797535 baseEnd_797535 := by
    simpa [prefixWord, tailWord_797535, baseEnd_797535] using wordTrace_append hprefix tailTrace_797535
  have hstable : (prefixWord ++ tailWord_797535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797535).length < 2 ^ (prefixWord ++ tailWord_797535).sum := by decide
  have hdescent : baseEnd_797535 < baseStart_797535 := by decide
  rcases family_descends (prefixWord ++ tailWord_797535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797539 : List Nat := [1, 1, 1, 5, 3, 2, 2, 1, 3, 4]
def baseStart_797539 : Nat := 118140960795 + 797539 * 2 ^ 59
def prefixEnd_797539 : Nat := 4983230072969 + 3 ^ 40 * 797539 * 2
def baseEnd_797539 : Nat := 136506949235420119564897

theorem tailTrace_797539 : CollatzResearch.WordTrace tailWord_797539 prefixEnd_797539 136506949235420119564897 := by
  unfold tailWord_797539
  simp only [CollatzResearch.WordTrace]
  refine ⟨29088637057659886662171671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19392424705106591108114447 29088637057659886662171671)
  ·
    refine ⟨43632955586489829993257507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29088637057659886662171671 43632955586489829993257507)
    ·
      refine ⟨65449433379734744989886261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43632955586489829993257507 65449433379734744989886261)
      ·
        refine ⟨6135884379350132342801837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65449433379734744989886261 6135884379350132342801837)
        ·
          refine ⟨2300956642256299628550689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6135884379350132342801837 2300956642256299628550689)
          ·
            refine ⟨1725717481692224721413017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2300956642256299628550689 1725717481692224721413017)
            ·
              refine ⟨1294288111269168541059763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1725717481692224721413017 1294288111269168541059763)
              ·
                refine ⟨1941432166903752811589645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1294288111269168541059763 1941432166903752811589645)
                ·
                  refine ⟨728037062588907304346117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1941432166903752811589645 728037062588907304346117)
                  ·
                    refine ⟨136506949235420119564897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 728037062588907304346117 136506949235420119564897)
                    ·
                      rfl

theorem cell23_797539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 1, 3, 4].length) (baseStart_797539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_797539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_797539 prefixEnd_797539 := by exact prefixLift 797539
  have htrace : WordTrace (prefixWord ++ tailWord_797539) baseStart_797539 baseEnd_797539 := by
    simpa [prefixWord, tailWord_797539, baseEnd_797539] using wordTrace_append hprefix tailTrace_797539
  have hstable : (prefixWord ++ tailWord_797539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797539).length < 2 ^ (prefixWord ++ tailWord_797539).sum := by decide
  have hdescent : baseEnd_797539 < baseStart_797539 := by decide
  rcases family_descends (prefixWord ++ tailWord_797539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797589 : List Nat := [1, 3, 2, 1, 1, 4, 1, 1, 4, 3, 2]
def baseStart_797589 : Nat := 118140960795 + 797589 * 2 ^ 59
def prefixEnd_797589 : Nat := 4983230072969 + 3 ^ 40 * 797589 * 2
def baseEnd_797589 : Nat := 409546521738985163069461

theorem tailTrace_797589 : CollatzResearch.WordTrace tailWord_797589 prefixEnd_797589 409546521738985163069461 := by
  unfold tailWord_797589
  simp only [CollatzResearch.WordTrace]
  refine ⟨29090460707478745201491821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19393640471652496800994547 29090460707478745201491821)
  ·
    refine ⟨10908922765304529450559433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29090460707478745201491821 10908922765304529450559433)
    ·
      refine ⟨8181692073978397087919575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10908922765304529450559433 8181692073978397087919575)
      ·
        refine ⟨12272538110967595631879363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8181692073978397087919575 12272538110967595631879363)
        ·
          refine ⟨18408807166451393447819045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12272538110967595631879363 18408807166451393447819045)
          ·
            refine ⟨3451651343709636271466071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18408807166451393447819045 3451651343709636271466071)
            ·
              refine ⟨5177477015564454407199107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3451651343709636271466071 5177477015564454407199107)
              ·
                refine ⟨7766215523346681610798661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5177477015564454407199107 7766215523346681610798661)
                ·
                  refine ⟨1456165410627502802024749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7766215523346681610798661 1456165410627502802024749)
                  ·
                    refine ⟨546062028985313550759281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1456165410627502802024749 546062028985313550759281)
                    ·
                      refine ⟨409546521738985163069461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 546062028985313550759281 409546521738985163069461)
                      ·
                        rfl

theorem cell23_797589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 4, 3, 2].length) (baseStart_797589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_797589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_797589 prefixEnd_797589 := by exact prefixLift 797589
  have htrace : WordTrace (prefixWord ++ tailWord_797589) baseStart_797589 baseEnd_797589 := by
    simpa [prefixWord, tailWord_797589, baseEnd_797589] using wordTrace_append hprefix tailTrace_797589
  have hstable : (prefixWord ++ tailWord_797589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797589).length < 2 ^ (prefixWord ++ tailWord_797589).sum := by decide
  have hdescent : baseEnd_797589 < baseStart_797589 := by decide
  rcases family_descends (prefixWord ++ tailWord_797589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797590 : List Nat := [5, 3, 1, 1, 1, 3, 1, 1, 3, 4]
def baseStart_797590 : Nat := 118140960795 + 797590 * 2 ^ 59
def prefixEnd_797590 : Nat := 4983230072969 + 3 ^ 40 * 797590 * 2
def baseEnd_797590 : Nat := 136515678406546553052319

theorem tailTrace_797590 : CollatzResearch.WordTrace tailWord_797590 prefixEnd_797590 136515678406546553052319 := by
  unfold tailWord_797590
  simp only [CollatzResearch.WordTrace]
  refine ⟨1818156073779695148267389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19393664786983414914852149 1818156073779695148267389)
  ·
    refine ⟨681808527667385680600271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1818156073779695148267389 681808527667385680600271)
    ·
      refine ⟨1022712791501078520900407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 681808527667385680600271 1022712791501078520900407)
      ·
        refine ⟨1534069187251617781350611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1022712791501078520900407 1534069187251617781350611)
        ·
          refine ⟨2301103780877426672025917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1534069187251617781350611 2301103780877426672025917)
          ·
            refine ⟨862913917829035002009719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2301103780877426672025917 862913917829035002009719)
            ·
              refine ⟨1294370876743552503014579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 862913917829035002009719 1294370876743552503014579)
              ·
                refine ⟨1941556315115328754521869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1294370876743552503014579 1941556315115328754521869)
                ·
                  refine ⟨728083618168248282945701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1941556315115328754521869 728083618168248282945701)
                  ·
                    refine ⟨136515678406546553052319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 728083618168248282945701 136515678406546553052319)
                    ·
                      rfl

theorem cell23_797590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_797590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_797590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_797590 prefixEnd_797590 := by exact prefixLift 797590
  have htrace : WordTrace (prefixWord ++ tailWord_797590) baseStart_797590 baseEnd_797590 := by
    simpa [prefixWord, tailWord_797590, baseEnd_797590] using wordTrace_append hprefix tailTrace_797590
  have hstable : (prefixWord ++ tailWord_797590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797590).length < 2 ^ (prefixWord ++ tailWord_797590).sum := by decide
  have hdescent : baseEnd_797590 < baseStart_797590 := by decide
  rcases family_descends (prefixWord ++ tailWord_797590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797629 : List Nat := [1, 4, 1, 2, 4, 1, 1, 2, 1, 6]
def baseStart_797629 : Nat := 118140960795 + 797629 * 2 ^ 59
def prefixEnd_797629 : Nat := 4983230072969 + 3 ^ 40 * 797629 * 2
def baseEnd_797629 : Nat := 136522353655055002189759

theorem tailTrace_797629 : CollatzResearch.WordTrace tailWord_797629 prefixEnd_797629 136522353655055002189759 := by
  unfold tailWord_797629
  simp only [CollatzResearch.WordTrace]
  refine ⟨29091919627333832032947941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19394613084889221355298627 29091919627333832032947941)
  ·
    refine ⟨5454734930125093506177739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29091919627333832032947941 5454734930125093506177739)
    ·
      refine ⟨8182102395187640259266609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5454734930125093506177739 8182102395187640259266609)
      ·
        refine ⟨6136576796390730194449957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8182102395187640259266609 6136576796390730194449957)
        ·
          refine ⟨1150608149323261911459367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6136576796390730194449957 1150608149323261911459367)
          ·
            refine ⟨1725912223984892867189051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1150608149323261911459367 1725912223984892867189051)
            ·
              refine ⟨2588868335977339300783577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1725912223984892867189051 2588868335977339300783577)
              ·
                refine ⟨1941651251983004475587683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2588868335977339300783577 1941651251983004475587683)
                ·
                  refine ⟨2912476877974506713381525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1941651251983004475587683 2912476877974506713381525)
                  ·
                    refine ⟨136522353655055002189759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2912476877974506713381525 136522353655055002189759)
                    ·
                      rfl

theorem cell23_797629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 2, 1, 6].length) (baseStart_797629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_797629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_797629 prefixEnd_797629 := by exact prefixLift 797629
  have htrace : WordTrace (prefixWord ++ tailWord_797629) baseStart_797629 baseEnd_797629 := by
    simpa [prefixWord, tailWord_797629, baseEnd_797629] using wordTrace_append hprefix tailTrace_797629
  have hstable : (prefixWord ++ tailWord_797629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797629).length < 2 ^ (prefixWord ++ tailWord_797629).sum := by decide
  have hdescent : baseEnd_797629 < baseStart_797629 := by decide
  rcases family_descends (prefixWord ++ tailWord_797629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797632 : List Nat := [2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 4]
def baseStart_797632 : Nat := 118140960795 + 797632 * 2 ^ 59
def prefixEnd_797632 : Nat := 4983230072969 + 3 ^ 40 * 797632 * 2
def baseEnd_797632 : Nat := 409568601407128494831763

theorem tailTrace_797632 : CollatzResearch.WordTrace tailWord_797632 prefixEnd_797632 409568601407128494831763 := by
  unfold tailWord_797632
  simp only [CollatzResearch.WordTrace]
  refine ⟨14546014523161481772653575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19394686030881975696871433 14546014523161481772653575)
  ·
    refine ⟨21819021784742222658980363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14546014523161481772653575 21819021784742222658980363)
    ·
      refine ⟨32728532677113333988470545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21819021784742222658980363 32728532677113333988470545)
      ·
        refine ⟨24546399507835000491352909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32728532677113333988470545 24546399507835000491352909)
        ·
          refine ⟨9204899815438125184257341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24546399507835000491352909 9204899815438125184257341)
          ·
            refine ⟨3451837430789296944096503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9204899815438125184257341 3451837430789296944096503)
            ·
              refine ⟨5177756146183945416144755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3451837430789296944096503 5177756146183945416144755)
              ·
                refine ⟨7766634219275918124217133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5177756146183945416144755 7766634219275918124217133)
                ·
                  refine ⟨2912487832228469296581425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7766634219275918124217133 2912487832228469296581425)
                  ·
                    refine ⟨2184365874171351972436069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2912487832228469296581425 2184365874171351972436069)
                    ·
                      refine ⟨409568601407128494831763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2184365874171351972436069 409568601407128494831763)
                      ·
                        rfl

theorem cell23_797632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 4].length) (baseStart_797632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_797632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_797632 prefixEnd_797632 := by exact prefixLift 797632
  have htrace : WordTrace (prefixWord ++ tailWord_797632) baseStart_797632 baseEnd_797632 := by
    simpa [prefixWord, tailWord_797632, baseEnd_797632] using wordTrace_append hprefix tailTrace_797632
  have hstable : (prefixWord ++ tailWord_797632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797632).length < 2 ^ (prefixWord ++ tailWord_797632).sum := by decide
  have hdescent : baseEnd_797632 < baseStart_797632 := by decide
  rcases family_descends (prefixWord ++ tailWord_797632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797639 : List Nat := [1, 1, 4, 1, 1, 2, 2, 5, 1, 2, 3]
def baseStart_797639 : Nat := 118140960795 + 797639 * 2 ^ 59
def prefixEnd_797639 : Nat := 4983230072969 + 3 ^ 40 * 797639 * 2
def baseEnd_797639 : Nat := 409572195771709967444231

theorem tailTrace_797639 : CollatzResearch.WordTrace tailWord_797639 prefixEnd_797639 409572195771709967444231 := by
  unfold tailWord_797639
  simp only [CollatzResearch.WordTrace]
  refine ⟨29092284357297603740811971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19394856238198402493874647 29092284357297603740811971)
  ·
    refine ⟨43638426535946405611217957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29092284357297603740811971 43638426535946405611217957)
    ·
      refine ⟨8182204975489951052103367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43638426535946405611217957 8182204975489951052103367)
      ·
        refine ⟨12273307463234926578155051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8182204975489951052103367 12273307463234926578155051)
        ·
          refine ⟨18409961194852389867232577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12273307463234926578155051 18409961194852389867232577)
          ·
            refine ⟨13807470896139292400424433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18409961194852389867232577 13807470896139292400424433)
            ·
              refine ⟨10355603172104469300318325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13807470896139292400424433 10355603172104469300318325)
              ·
                refine ⟨970837797384793996904843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10355603172104469300318325 970837797384793996904843)
                ·
                  refine ⟨1456256696077190995357265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 970837797384793996904843 1456256696077190995357265)
                  ·
                    refine ⟨1092192522057893246517949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1456256696077190995357265 1092192522057893246517949)
                    ·
                      refine ⟨409572195771709967444231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1092192522057893246517949 409572195771709967444231)
                      ·
                        rfl

theorem cell23_797639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 5, 1, 2, 3].length) (baseStart_797639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_797639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_797639 prefixEnd_797639 := by exact prefixLift 797639
  have htrace : WordTrace (prefixWord ++ tailWord_797639) baseStart_797639 baseEnd_797639 := by
    simpa [prefixWord, tailWord_797639, baseEnd_797639] using wordTrace_append hprefix tailTrace_797639
  have hstable : (prefixWord ++ tailWord_797639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797639).length < 2 ^ (prefixWord ++ tailWord_797639).sum := by decide
  have hdescent : baseEnd_797639 < baseStart_797639 := by decide
  rcases family_descends (prefixWord ++ tailWord_797639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797646 : List Nat := [4, 1, 1, 1, 2, 4, 2, 2, 2, 4]
def baseStart_797646 : Nat := 118140960795 + 797646 * 2 ^ 59
def prefixEnd_797646 : Nat := 4983230072969 + 3 ^ 40 * 797646 * 2
def baseEnd_797646 : Nat := 136525263378763813352233

theorem tailTrace_797646 : CollatzResearch.WordTrace tailWord_797646 prefixEnd_797646 136525263378763813352233 := by
  unfold tailWord_797646
  simp only [CollatzResearch.WordTrace]
  refine ⟨3636567458534030492039599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19395026445514829290877861 3636567458534030492039599)
  ·
    refine ⟨5454851187801045738059399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3636567458534030492039599 5454851187801045738059399)
    ·
      refine ⟨8182276781701568607089099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5454851187801045738059399 8182276781701568607089099)
      ·
        refine ⟨12273415172552352910633649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8182276781701568607089099 12273415172552352910633649)
        ·
          refine ⟨9205061379414264682975237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12273415172552352910633649 9205061379414264682975237)
          ·
            refine ⟨1725949008640174628057857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9205061379414264682975237 1725949008640174628057857)
            ·
              refine ⟨1294461756480130971043393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1725949008640174628057857 1294461756480130971043393)
              ·
                refine ⟨970846317360098228282545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1294461756480130971043393 970846317360098228282545)
                ·
                  refine ⟨728134738020073671211909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 970846317360098228282545 728134738020073671211909)
                  ·
                    refine ⟨136525263378763813352233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 728134738020073671211909 136525263378763813352233)
                    ·
                      rfl

theorem cell23_797646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 2, 2, 4].length) (baseStart_797646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_797646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_797646 prefixEnd_797646 := by exact prefixLift 797646
  have htrace : WordTrace (prefixWord ++ tailWord_797646) baseStart_797646 baseEnd_797646 := by
    simpa [prefixWord, tailWord_797646, baseEnd_797646] using wordTrace_append hprefix tailTrace_797646
  have hstable : (prefixWord ++ tailWord_797646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797646).length < 2 ^ (prefixWord ++ tailWord_797646).sum := by decide
  have hdescent : baseEnd_797646 < baseStart_797646 := by decide
  rcases family_descends (prefixWord ++ tailWord_797646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797666 : List Nat := [3, 3, 3, 1, 1, 1, 1, 3, 1, 2, 4]
def baseStart_797666 : Nat := 118140960795 + 797666 * 2 ^ 59
def prefixEnd_797666 : Nat := 4983230072969 + 3 ^ 40 * 797666 * 2
def baseEnd_797666 : Nat := 409586059749381361806607

theorem tailTrace_797666 : CollatzResearch.WordTrace tailWord_797666 prefixEnd_797666 409586059749381361806607 := by
  unfold tailWord_797666
  simp only [CollatzResearch.WordTrace]
  refine ⟨7273317282049946838011213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19395512752133191568029901 7273317282049946838011213)
  ·
    refine ⟨2727493980768730064254205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7273317282049946838011213 2727493980768730064254205)
    ·
      refine ⟨1022810242788273774095327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2727493980768730064254205 1022810242788273774095327)
      ·
        refine ⟨1534215364182410661142991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1022810242788273774095327 1534215364182410661142991)
        ·
          refine ⟨2301323046273615991714487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1534215364182410661142991 2301323046273615991714487)
          ·
            refine ⟨3451984569410423987571731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2301323046273615991714487 3451984569410423987571731)
            ·
              refine ⟨5177976854115635981357597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3451984569410423987571731 5177976854115635981357597)
              ·
                refine ⟨1941741320293363493009099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5177976854115635981357597 1941741320293363493009099)
                ·
                  refine ⟨2912611980440045239513649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1941741320293363493009099 2912611980440045239513649)
                  ·
                    refine ⟨2184458985330033929635237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2912611980440045239513649 2184458985330033929635237)
                    ·
                      refine ⟨409586059749381361806607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2184458985330033929635237 409586059749381361806607)
                      ·
                        rfl

theorem cell23_797666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_797666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_797666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_797666 prefixEnd_797666 := by exact prefixLift 797666
  have htrace : WordTrace (prefixWord ++ tailWord_797666) baseStart_797666 baseEnd_797666 := by
    simpa [prefixWord, tailWord_797666, baseEnd_797666] using wordTrace_append hprefix tailTrace_797666
  have hstable : (prefixWord ++ tailWord_797666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797666).length < 2 ^ (prefixWord ++ tailWord_797666).sum := by decide
  have hdescent : baseEnd_797666 < baseStart_797666 := by decide
  rcases family_descends (prefixWord ++ tailWord_797666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797684 : List Nat := [2, 6, 2, 1, 1, 2, 2, 1, 1, 5]
def baseStart_797684 : Nat := 118140960795 + 797684 * 2 ^ 59
def prefixEnd_797684 : Nat := 4983230072969 + 3 ^ 40 * 797684 * 2
def baseEnd_797684 : Nat := 136531767467054097127175

theorem tailTrace_797684 : CollatzResearch.WordTrace tailWord_797684 prefixEnd_797684 136531767467054097127175 := by
  unfold tailWord_797684
  simp only [CollatzResearch.WordTrace]
  refine ⟨14546962821067288213100053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19395950428089717617466737 14546962821067288213100053)
  ·
    refine ⟨681888882237529134989065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14546962821067288213100053 681888882237529134989065)
    ·
      refine ⟨511416661678146851241799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 681888882237529134989065 511416661678146851241799)
      ·
        refine ⟨767124992517220276862699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 511416661678146851241799 767124992517220276862699)
        ·
          refine ⟨1150687488775830415294049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 767124992517220276862699 1150687488775830415294049)
          ·
            refine ⟨863015616581872811470537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1150687488775830415294049 863015616581872811470537)
            ·
              refine ⟨647261712436404608602903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 863015616581872811470537 647261712436404608602903)
              ·
                refine ⟨970892568654606912904355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 647261712436404608602903 970892568654606912904355)
                ·
                  refine ⟨1456338852981910369356533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 970892568654606912904355 1456338852981910369356533)
                  ·
                    refine ⟨136531767467054097127175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1456338852981910369356533 136531767467054097127175)
                    ·
                      rfl

theorem cell23_797684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_797684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_797684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_797684 prefixEnd_797684 := by exact prefixLift 797684
  have htrace : WordTrace (prefixWord ++ tailWord_797684) baseStart_797684 baseEnd_797684 := by
    simpa [prefixWord, tailWord_797684, baseEnd_797684] using wordTrace_append hprefix tailTrace_797684
  have hstable : (prefixWord ++ tailWord_797684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797684).length < 2 ^ (prefixWord ++ tailWord_797684).sum := by decide
  have hdescent : baseEnd_797684 < baseStart_797684 := by decide
  rcases family_descends (prefixWord ++ tailWord_797684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797686 : List Nat := [5, 1, 1, 1, 3, 1, 2, 2, 1, 3, 3]
def baseStart_797686 : Nat := 118140960795 + 797686 * 2 ^ 59
def prefixEnd_797686 : Nat := 4983230072969 + 3 ^ 40 * 797686 * 2
def baseEnd_797686 : Nat := 409596329362471283556515

theorem tailTrace_797686 : CollatzResearch.WordTrace tailWord_797686 prefixEnd_797686 409596329362471283556515 := by
  unfold tailWord_797686
  simp only [CollatzResearch.WordTrace]
  refine ⟨1818374911757958172985807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19395999058751553845181941 1818374911757958172985807)
  ·
    refine ⟨2727562367636937259478711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1818374911757958172985807 2727562367636937259478711)
    ·
      refine ⟨4091343551455405889218067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2727562367636937259478711 4091343551455405889218067)
      ·
        refine ⟨6137015327183108833827101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4091343551455405889218067 6137015327183108833827101)
        ·
          refine ⟨2301380747693665812685163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6137015327183108833827101 2301380747693665812685163)
          ·
            refine ⟨3452071121540498719027745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2301380747693665812685163 3452071121540498719027745)
            ·
              refine ⟨2589053341155374039270809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3452071121540498719027745 2589053341155374039270809)
              ·
                refine ⟨1941790005866530529453107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2589053341155374039270809 1941790005866530529453107)
                ·
                  refine ⟨2912685008799795794179661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1941790005866530529453107 2912685008799795794179661)
                  ·
                    refine ⟨1092256878299923422817373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2912685008799795794179661 1092256878299923422817373)
                    ·
                      refine ⟨409596329362471283556515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1092256878299923422817373 409596329362471283556515)
                      ·
                        rfl

theorem cell23_797686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_797686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_797686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_797686 prefixEnd_797686 := by exact prefixLift 797686
  have htrace : WordTrace (prefixWord ++ tailWord_797686) baseStart_797686 baseEnd_797686 := by
    simpa [prefixWord, tailWord_797686, baseEnd_797686] using wordTrace_append hprefix tailTrace_797686
  have hstable : (prefixWord ++ tailWord_797686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797686).length < 2 ^ (prefixWord ++ tailWord_797686).sum := by decide
  have hdescent : baseEnd_797686 < baseStart_797686 := by decide
  rcases family_descends (prefixWord ++ tailWord_797686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797719 : List Nat := [1, 1, 3, 5, 1, 1, 2, 1, 2, 6]
def baseStart_797719 : Nat := 118140960795 + 797719 * 2 ^ 59
def prefixEnd_797719 : Nat := 4983230072969 + 3 ^ 40 * 797719 * 2
def baseEnd_797719 : Nat := 136537758074689884814621

theorem tailTrace_797719 : CollatzResearch.WordTrace tailWord_797719 prefixEnd_797719 136537758074689884814621 := by
  unfold tailWord_797719
  simp only [CollatzResearch.WordTrace]
  refine ⟨29095202197007777403724211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19396801464671851602482807 29095202197007777403724211)
  ·
    refine ⟨43642803295511666105586317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29095202197007777403724211 43642803295511666105586317)
    ·
      refine ⟨16366051235816874789594869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43642803295511666105586317 16366051235816874789594869)
      ·
        refine ⟨1534317303357832011524519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16366051235816874789594869 1534317303357832011524519)
        ·
          refine ⟨2301475955036748017286779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1534317303357832011524519 2301475955036748017286779)
          ·
            refine ⟨3452213932555122025930169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2301475955036748017286779 3452213932555122025930169)
            ·
              refine ⟨2589160449416341519447627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3452213932555122025930169 2589160449416341519447627)
              ·
                refine ⟨3883740674124512279171441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2589160449416341519447627 3883740674124512279171441)
                ·
                  refine ⟨2912805505593384209378581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3883740674124512279171441 2912805505593384209378581)
                  ·
                    refine ⟨136537758074689884814621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2912805505593384209378581 136537758074689884814621)
                    ·
                      rfl

theorem cell23_797719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 2, 6].length) (baseStart_797719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_797719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_797719 prefixEnd_797719 := by exact prefixLift 797719
  have htrace : WordTrace (prefixWord ++ tailWord_797719) baseStart_797719 baseEnd_797719 := by
    simpa [prefixWord, tailWord_797719, baseEnd_797719] using wordTrace_append hprefix tailTrace_797719
  have hstable : (prefixWord ++ tailWord_797719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797719).length < 2 ^ (prefixWord ++ tailWord_797719).sum := by decide
  have hdescent : baseEnd_797719 < baseStart_797719 := by decide
  rcases family_descends (prefixWord ++ tailWord_797719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797809 : List Nat := [1, 2, 2, 2, 1, 1, 2, 1, 7, 4]
def baseStart_797809 : Nat := 118140960795 + 797809 * 2 ^ 59
def prefixEnd_797809 : Nat := 4983230072969 + 3 ^ 40 * 797809 * 2
def baseEnd_797809 : Nat := 136553162494324767439483

theorem tailTrace_797809 : CollatzResearch.WordTrace tailWord_797809 prefixEnd_797809 136553162494324767439483 := by
  unfold tailWord_797809
  simp only [CollatzResearch.WordTrace]
  refine ⟨29098484766681722774500481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19398989844454481849666987 29098484766681722774500481)
  ·
    refine ⟨21823863575011292080875361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29098484766681722774500481 21823863575011292080875361)
    ·
      refine ⟨16367897681258469060656521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21823863575011292080875361 16367897681258469060656521)
      ·
        refine ⟨12275923260943851795492391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16367897681258469060656521 12275923260943851795492391)
        ·
          refine ⟨18413884891415777693238587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12275923260943851795492391 18413884891415777693238587)
          ·
            refine ⟨27620827337123666539857881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18413884891415777693238587 27620827337123666539857881)
            ·
              refine ⟨20715620502842749904893411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27620827337123666539857881 20715620502842749904893411)
              ·
                refine ⟨31073430754264124857340117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20715620502842749904893411 31073430754264124857340117)
                ·
                  refine ⟨728283533303065426343909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 31073430754264124857340117 728283533303065426343909)
                  ·
                    refine ⟨136553162494324767439483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 728283533303065426343909 136553162494324767439483)
                    ·
                      rfl

theorem cell23_797809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 7, 4].length) (baseStart_797809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_797809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_797809 prefixEnd_797809 := by exact prefixLift 797809
  have htrace : WordTrace (prefixWord ++ tailWord_797809) baseStart_797809 baseEnd_797809 := by
    simpa [prefixWord, tailWord_797809, baseEnd_797809] using wordTrace_append hprefix tailTrace_797809
  have hstable : (prefixWord ++ tailWord_797809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797809).length < 2 ^ (prefixWord ++ tailWord_797809).sum := by decide
  have hdescent : baseEnd_797809 < baseStart_797809 := by decide
  rcases family_descends (prefixWord ++ tailWord_797809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797860 : List Nat := [2, 3, 1, 2, 3, 2, 2, 3, 1, 4]
def baseStart_797860 : Nat := 118140960795 + 797860 * 2 ^ 59
def prefixEnd_797860 : Nat := 4983230072969 + 3 ^ 40 * 797860 * 2
def baseEnd_797860 : Nat := 136561891665451200926905

theorem tailTrace_797860 : CollatzResearch.WordTrace tailWord_797860 prefixEnd_797860 136561891665451200926905 := by
  unfold tailWord_797860
  simp only [CollatzResearch.WordTrace]
  refine ⟨14550172444748479242303517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19400229926331305656404689 14550172444748479242303517)
  ·
    refine ⟨5456314666780679715863819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14550172444748479242303517 5456314666780679715863819)
    ·
      refine ⟨8184472000171019573795729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5456314666780679715863819 8184472000171019573795729)
      ·
        refine ⟨6138354000128264680346797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8184472000171019573795729 6138354000128264680346797)
        ·
          refine ⟨2301882750048099255130049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6138354000128264680346797 2301882750048099255130049)
          ·
            refine ⟨1726412062536074441347537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2301882750048099255130049 1726412062536074441347537)
            ·
              refine ⟨1294809046902055831010653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1726412062536074441347537 1294809046902055831010653)
              ·
                refine ⟨485553392588270936628995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1294809046902055831010653 485553392588270936628995)
                ·
                  refine ⟨728330088882406404943493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 485553392588270936628995 728330088882406404943493)
                  ·
                    refine ⟨136561891665451200926905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 728330088882406404943493 136561891665451200926905)
                    ·
                      rfl

theorem cell23_797860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 3, 1, 4].length) (baseStart_797860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_797860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_797860 prefixEnd_797860 := by exact prefixLift 797860
  have htrace : WordTrace (prefixWord ++ tailWord_797860) baseStart_797860 baseEnd_797860 := by
    simpa [prefixWord, tailWord_797860, baseEnd_797860] using wordTrace_append hprefix tailTrace_797860
  have hstable : (prefixWord ++ tailWord_797860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797860).length < 2 ^ (prefixWord ++ tailWord_797860).sum := by decide
  have hdescent : baseEnd_797860 < baseStart_797860 := by decide
  rcases family_descends (prefixWord ++ tailWord_797860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797873 : List Nat := [1, 2, 2, 5, 1, 3, 1, 2, 6]
def baseStart_797873 : Nat := 118140960795 + 797873 * 2 ^ 59
def prefixEnd_797873 : Nat := 4983230072969 + 3 ^ 40 * 797873 * 2
def baseEnd_797873 : Nat := 45521372249429116879795

theorem tailTrace_797873 : CollatzResearch.WordTrace tailWord_797873 prefixEnd_797873 45521372249429116879795 := by
  unfold tailWord_797873
  simp only [CollatzResearch.WordTrace]
  refine ⟨29100819038449861704830273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19400546025633241136553515 29100819038449861704830273)
  ·
    refine ⟨21825614278837396278622705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29100819038449861704830273 21825614278837396278622705)
    ·
      refine ⟨16369210709128047208967029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21825614278837396278622705 16369210709128047208967029)
      ·
        refine ⟨1534613503980754425840659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16369210709128047208967029 1534613503980754425840659)
        ·
          refine ⟨2301920255971131638760989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1534613503980754425840659 2301920255971131638760989)
          ·
            refine ⟨863220095989174364535371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2301920255971131638760989 863220095989174364535371)
            ·
              refine ⟨1294830143983761546803057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 863220095989174364535371 1294830143983761546803057)
              ·
                refine ⟨971122607987821160102293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1294830143983761546803057 971122607987821160102293)
                ·
                  refine ⟨45521372249429116879795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 971122607987821160102293 45521372249429116879795)
                  ·
                    rfl

theorem cell23_797873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 2, 6].length) (baseStart_797873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_797873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_797873 prefixEnd_797873 := by exact prefixLift 797873
  have htrace : WordTrace (prefixWord ++ tailWord_797873) baseStart_797873 baseEnd_797873 := by
    simpa [prefixWord, tailWord_797873, baseEnd_797873] using wordTrace_append hprefix tailTrace_797873
  have hstable : (prefixWord ++ tailWord_797873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797873).length < 2 ^ (prefixWord ++ tailWord_797873).sum := by decide
  have hdescent : baseEnd_797873 < baseStart_797873 := by decide
  rcases family_descends (prefixWord ++ tailWord_797873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797899 : List Nat := [1, 1, 1, 1, 3, 2, 2, 5, 1, 6]
def baseStart_797899 : Nat := 118140960795 + 797899 * 2 ^ 59
def prefixEnd_797899 : Nat := 4983230072969 + 3 ^ 40 * 797899 * 2
def baseEnd_797899 : Nat := 136568566913959650064345

theorem tailTrace_797899 : CollatzResearch.WordTrace tailWord_797899 prefixEnd_797899 136568566913959650064345 := by
  unfold tailWord_797899
  simp only [CollatzResearch.WordTrace]
  refine ⟨29101767336355668145276751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19401178224237112096851167 29101767336355668145276751)
  ·
    refine ⟨43652651004533502217915127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29101767336355668145276751 43652651004533502217915127)
    ·
      refine ⟨65478976506800253326872691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43652651004533502217915127 65478976506800253326872691)
      ·
        refine ⟨98218464760200379990309037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65478976506800253326872691 98218464760200379990309037)
        ·
          refine ⟨36831924285075142496365889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98218464760200379990309037 36831924285075142496365889)
          ·
            refine ⟨27623943213806356872274417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36831924285075142496365889 27623943213806356872274417)
            ·
              refine ⟨20717957410354767654205813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27623943213806356872274417 20717957410354767654205813)
              ·
                refine ⟨1942308507220759467581795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20717957410354767654205813 1942308507220759467581795)
                ·
                  refine ⟨2913462760831139201372693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1942308507220759467581795 2913462760831139201372693)
                  ·
                    refine ⟨136568566913959650064345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2913462760831139201372693 136568566913959650064345)
                    ·
                      rfl

theorem cell23_797899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 5, 1, 6].length) (baseStart_797899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_797899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_797899 prefixEnd_797899 := by exact prefixLift 797899
  have htrace : WordTrace (prefixWord ++ tailWord_797899) baseStart_797899 baseEnd_797899 := by
    simpa [prefixWord, tailWord_797899, baseEnd_797899] using wordTrace_append hprefix tailTrace_797899
  have hstable : (prefixWord ++ tailWord_797899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797899).length < 2 ^ (prefixWord ++ tailWord_797899).sum := by decide
  have hdescent : baseEnd_797899 < baseStart_797899 := by decide
  rcases family_descends (prefixWord ++ tailWord_797899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797933 : List Nat := [1, 5, 1, 2, 2, 1, 2, 1, 4, 4]
def baseStart_797933 : Nat := 118140960795 + 797933 * 2 ^ 59
def prefixEnd_797933 : Nat := 4983230072969 + 3 ^ 40 * 797933 * 2
def baseEnd_797933 : Nat := 136574386361377272389293

theorem tailTrace_797933 : CollatzResearch.WordTrace tailWord_797933 prefixEnd_797933 136574386361377272389293 := by
  unfold tailWord_797933
  simp only [CollatzResearch.WordTrace]
  refine ⟨29103007418232491952014453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19402004945488327968009635 29103007418232491952014453)
  ·
    refine ⟨2728406945459296120501355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29103007418232491952014453 2728406945459296120501355)
    ·
      refine ⟨4092610418188944180752033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2728406945459296120501355 4092610418188944180752033)
      ·
        refine ⟨3069457813641708135564025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4092610418188944180752033 3069457813641708135564025)
        ·
          refine ⟨2302093360231281101673019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3069457813641708135564025 2302093360231281101673019)
          ·
            refine ⟨3453140040346921652509529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2302093360231281101673019 3453140040346921652509529)
            ·
              refine ⟨2589855030260191239382147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3453140040346921652509529 2589855030260191239382147)
              ·
                refine ⟨3884782545390286859073221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2589855030260191239382147 3884782545390286859073221)
                ·
                  refine ⟨728396727260678786076229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3884782545390286859073221 728396727260678786076229)
                  ·
                    refine ⟨136574386361377272389293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 728396727260678786076229 136574386361377272389293)
                    ·
                      rfl

theorem cell23_797933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_797933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_797933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_797933 prefixEnd_797933 := by exact prefixLift 797933
  have htrace : WordTrace (prefixWord ++ tailWord_797933) baseStart_797933 baseEnd_797933 := by
    simpa [prefixWord, tailWord_797933, baseEnd_797933] using wordTrace_append hprefix tailTrace_797933
  have hstable : (prefixWord ++ tailWord_797933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797933).length < 2 ^ (prefixWord ++ tailWord_797933).sum := by decide
  have hdescent : baseEnd_797933 < baseStart_797933 := by decide
  rcases family_descends (prefixWord ++ tailWord_797933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797950 : List Nat := [4, 2, 2, 1, 1, 3, 1, 3, 2, 4]
def baseStart_797950 : Nat := 118140960795 + 797950 * 2 ^ 59
def prefixEnd_797950 : Nat := 4983230072969 + 3 ^ 40 * 797950 * 2
def baseEnd_797950 : Nat := 136577296085086083551767

theorem tailTrace_797950 : CollatzResearch.WordTrace tailWord_797950 prefixEnd_797950 136577296085086083551767 := by
  unfold tailWord_797950
  simp only [CollatzResearch.WordTrace]
  refine ⟨3637953432396362981922913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19402418306113935903588869 3637953432396362981922913)
  ·
    refine ⟨2728465074297272236442185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3637953432396362981922913 2728465074297272236442185)
    ·
      refine ⟨2046348805722954177331639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2728465074297272236442185 2046348805722954177331639)
      ·
        refine ⟨3069523208584431265997459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2046348805722954177331639 3069523208584431265997459)
        ·
          refine ⟨4604284812876646898996189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3069523208584431265997459 4604284812876646898996189)
          ·
            refine ⟨1726606804828742587123571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4604284812876646898996189 1726606804828742587123571)
            ·
              refine ⟨2589910207243113880685357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1726606804828742587123571 2589910207243113880685357)
              ·
                refine ⟨971216327716167705257009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2589910207243113880685357 971216327716167705257009)
                ·
                  refine ⟨728412245787125778942757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 971216327716167705257009 728412245787125778942757)
                  ·
                    refine ⟨136577296085086083551767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 728412245787125778942757 136577296085086083551767)
                    ·
                      rfl

theorem cell23_797950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_797950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_797950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_797950 prefixEnd_797950 := by exact prefixLift 797950
  have htrace : WordTrace (prefixWord ++ tailWord_797950) baseStart_797950 baseEnd_797950 := by
    simpa [prefixWord, tailWord_797950, baseEnd_797950] using wordTrace_append hprefix tailTrace_797950
  have hstable : (prefixWord ++ tailWord_797950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797950).length < 2 ^ (prefixWord ++ tailWord_797950).sum := by decide
  have hdescent : baseEnd_797950 < baseStart_797950 := by decide
  rcases family_descends (prefixWord ++ tailWord_797950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798016 : List Nat := [2, 1, 1, 2, 2, 1, 3, 2, 2, 4, 3]
def baseStart_798016 : Nat := 118140960795 + 798016 * 2 ^ 59
def prefixEnd_798016 : Nat := 4983230072969 + 3 ^ 40 * 798016 * 2
def baseEnd_798016 : Nat := 409765777978454992429997

theorem tailTrace_798016 : CollatzResearch.WordTrace tailWord_798016 prefixEnd_798016 409765777978454992429997 := by
  unfold tailWord_798016
  simp only [CollatzResearch.WordTrace]
  refine ⟨14553017338465898563642951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19404023117954531418190601 14553017338465898563642951)
  ·
    refine ⟨21829526007698847845464427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14553017338465898563642951 21829526007698847845464427)
    ·
      refine ⟨32744289011548271768196641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21829526007698847845464427 32744289011548271768196641)
      ·
        refine ⟨24558216758661203826147481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32744289011548271768196641 24558216758661203826147481)
        ·
          refine ⟨18418662568995902869610611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24558216758661203826147481 18418662568995902869610611)
          ·
            refine ⟨27627993853493854304415917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18418662568995902869610611 27627993853493854304415917)
            ·
              refine ⟨10360497695060195364155969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27627993853493854304415917 10360497695060195364155969)
              ·
                refine ⟨7770373271295146523116977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10360497695060195364155969 7770373271295146523116977)
                ·
                  refine ⟨5827779953471359892337733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7770373271295146523116977 5827779953471359892337733)
                  ·
                    refine ⟨1092708741275879979813325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5827779953471359892337733 1092708741275879979813325)
                    ·
                      refine ⟨409765777978454992429997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1092708741275879979813325 409765777978454992429997)
                      ·
                        rfl

theorem cell23_798016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 2, 4, 3].length) (baseStart_798016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_798016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_798016 prefixEnd_798016 := by exact prefixLift 798016
  have htrace : WordTrace (prefixWord ++ tailWord_798016) baseStart_798016 baseEnd_798016 := by
    simpa [prefixWord, tailWord_798016, baseEnd_798016] using wordTrace_append hprefix tailTrace_798016
  have hstable : (prefixWord ++ tailWord_798016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798016).length < 2 ^ (prefixWord ++ tailWord_798016).sum := by decide
  have hdescent : baseEnd_798016 < baseStart_798016 := by decide
  rcases family_descends (prefixWord ++ tailWord_798016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798030 : List Nat := [4, 1, 1, 1, 1, 1, 4, 2, 4, 2, 2]
def baseStart_798030 : Nat := 118140960795 + 798030 * 2 ^ 59
def prefixEnd_798030 : Nat := 4983230072969 + 3 ^ 40 * 798030 * 2
def baseEnd_798030 : Nat := 409772966707617937654933

theorem tailTrace_798030 : CollatzResearch.WordTrace tailWord_798030 prefixEnd_798030 409772966707617937654933 := by
  unfold tailWord_798030
  simp only [CollatzResearch.WordTrace]
  refine ⟨3638318162360134689786943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19404363532587385012197029 3638318162360134689786943)
  ·
    refine ⟨5457477243540202034680415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3638318162360134689786943 5457477243540202034680415)
    ·
      refine ⟨8186215865310303052020623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5457477243540202034680415 8186215865310303052020623)
      ·
        refine ⟨12279323797965454578030935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8186215865310303052020623 12279323797965454578030935)
        ·
          refine ⟨18418985696948181867046403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12279323797965454578030935 18418985696948181867046403)
          ·
            refine ⟨27628478545422272800569605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18418985696948181867046403 27628478545422272800569605)
            ·
              refine ⟨5180339727266676150106801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27628478545422272800569605 5180339727266676150106801)
              ·
                refine ⟨3885254795450007112580101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5180339727266676150106801 3885254795450007112580101)
                ·
                  refine ⟨728485274146876333608769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3885254795450007112580101 728485274146876333608769)
                  ·
                    refine ⟨546363955610157250206577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 728485274146876333608769 546363955610157250206577)
                    ·
                      refine ⟨409772966707617937654933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 546363955610157250206577 409772966707617937654933)
                      ·
                        rfl

theorem cell23_798030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 4, 2, 2].length) (baseStart_798030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_798030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_798030 prefixEnd_798030 := by exact prefixLift 798030
  have htrace : WordTrace (prefixWord ++ tailWord_798030) baseStart_798030 baseEnd_798030 := by
    simpa [prefixWord, tailWord_798030, baseEnd_798030] using wordTrace_append hprefix tailTrace_798030
  have hstable : (prefixWord ++ tailWord_798030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798030).length < 2 ^ (prefixWord ++ tailWord_798030).sum := by decide
  have hdescent : baseEnd_798030 < baseStart_798030 := by decide
  rcases family_descends (prefixWord ++ tailWord_798030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798036 : List Nat := [2, 4, 1, 1, 2, 1, 1, 2, 9]
def baseStart_798036 : Nat := 118140960795 + 798036 * 2 ^ 59
def prefixEnd_798036 : Nat := 4983230072969 + 3 ^ 40 * 798036 * 2
def baseEnd_798036 : Nat := 45530671954616101575545

theorem tailTrace_798036 : CollatzResearch.WordTrace tailWord_798036 prefixEnd_798036 45530671954616101575545 := by
  unfold tailWord_798036
  simp only [CollatzResearch.WordTrace]
  refine ⟨14553382068429670271506981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19404509424572893695342641 14553382068429670271506981)
  ·
    refine ⟨2728759137830563175907559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14553382068429670271506981 2728759137830563175907559)
    ·
      refine ⟨4093138706745844763861339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2728759137830563175907559 4093138706745844763861339)
      ·
        refine ⟨6139708060118767145792009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4093138706745844763861339 6139708060118767145792009)
        ·
          refine ⟨4604781045089075359344007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6139708060118767145792009 4604781045089075359344007)
          ·
            refine ⟨6907171567633613039016011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4604781045089075359344007 6907171567633613039016011)
            ·
              refine ⟨10360757351450419558524017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6907171567633613039016011 10360757351450419558524017)
              ·
                refine ⟨7770568013587814668893013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10360757351450419558524017 7770568013587814668893013)
                ·
                  refine ⟨45530671954616101575545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 7770568013587814668893013 45530671954616101575545)
                  ·
                    rfl

theorem cell23_798036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 9].length) (baseStart_798036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_798036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_798036 prefixEnd_798036 := by exact prefixLift 798036
  have htrace : WordTrace (prefixWord ++ tailWord_798036) baseStart_798036 baseEnd_798036 := by
    simpa [prefixWord, tailWord_798036, baseEnd_798036] using wordTrace_append hprefix tailTrace_798036
  have hstable : (prefixWord ++ tailWord_798036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798036).length < 2 ^ (prefixWord ++ tailWord_798036).sum := by decide
  have hdescent : baseEnd_798036 < baseStart_798036 := by decide
  rcases family_descends (prefixWord ++ tailWord_798036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798053 : List Nat := [1, 3, 1, 3, 1, 2, 1, 6, 5]
def baseStart_798053 : Nat := 118140960795 + 798053 * 2 ^ 59
def prefixEnd_798053 : Nat := 4983230072969 + 3 ^ 40 * 798053 * 2
def baseEnd_798053 : Nat := 45531641862519038629703

theorem tailTrace_798053 : CollatzResearch.WordTrace tailWord_798053 prefixEnd_798053 45531641862519038629703 := by
  unfold tailWord_798053
  simp only [CollatzResearch.WordTrace]
  refine ⟨29107384177797752446382813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19404922785198501630921875 29107384177797752446382813)
  ·
    refine ⟨10915269066674157167393555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29107384177797752446382813 10915269066674157167393555)
    ·
      refine ⟨16372903600011235751090333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10915269066674157167393555 16372903600011235751090333)
      ·
        refine ⟨6139838850004213406658875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16372903600011235751090333 6139838850004213406658875)
        ·
          refine ⟨9209758275006320109988313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6139838850004213406658875 9209758275006320109988313)
          ·
            refine ⟨6907318706254740082491235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9209758275006320109988313 6907318706254740082491235)
            ·
              refine ⟨10360978059382110123736853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6907318706254740082491235 10360978059382110123736853)
              ·
                refine ⟨485670846533536412050165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10360978059382110123736853 485670846533536412050165)
                ·
                  refine ⟨45531641862519038629703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 485670846533536412050165 45531641862519038629703)
                  ·
                    rfl

theorem cell23_798053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 6, 5].length) (baseStart_798053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_798053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_798053 prefixEnd_798053 := by exact prefixLift 798053
  have htrace : WordTrace (prefixWord ++ tailWord_798053) baseStart_798053 baseEnd_798053 := by
    simpa [prefixWord, tailWord_798053, baseEnd_798053] using wordTrace_append hprefix tailTrace_798053
  have hstable : (prefixWord ++ tailWord_798053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798053).length < 2 ^ (prefixWord ++ tailWord_798053).sum := by decide
  have hdescent : baseEnd_798053 < baseStart_798053 := by decide
  rcases family_descends (prefixWord ++ tailWord_798053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798066 : List Nat := [3, 2, 1, 2, 1, 2, 1, 1, 3, 7]
def baseStart_798066 : Nat := 118140960795 + 798066 * 2 ^ 59
def prefixEnd_798066 : Nat := 4983230072969 + 3 ^ 40 * 798066 * 2
def baseEnd_798066 : Nat := 136597150670393265601589

theorem tailTrace_798066 : CollatzResearch.WordTrace tailWord_798066 prefixEnd_798066 136597150670393265601589 := by
  unfold tailWord_798066
  simp only [CollatzResearch.WordTrace]
  refine ⟨7276964581687663916651513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19405238884500437111070701 7276964581687663916651513)
  ·
    refine ⟨5457723436265747937488635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7276964581687663916651513 5457723436265747937488635)
    ·
      refine ⟨8186585154398621906232953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5457723436265747937488635 8186585154398621906232953)
      ·
        refine ⟨6139938865798966429674715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8186585154398621906232953 6139938865798966429674715)
        ·
          refine ⟨9209908298698449644512073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6139938865798966429674715 9209908298698449644512073)
          ·
            refine ⟨6907431224023837233384055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9209908298698449644512073 6907431224023837233384055)
            ·
              refine ⟨10361146836035755850076083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6907431224023837233384055 10361146836035755850076083)
              ·
                refine ⟨15541720254053633775114125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10361146836035755850076083 15541720254053633775114125)
                ·
                  refine ⟨5828145095270112665667797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15541720254053633775114125 5828145095270112665667797)
                  ·
                    refine ⟨136597150670393265601589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5828145095270112665667797 136597150670393265601589)
                    ·
                      rfl

theorem cell23_798066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 3, 7].length) (baseStart_798066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_798066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_798066 prefixEnd_798066 := by exact prefixLift 798066
  have htrace : WordTrace (prefixWord ++ tailWord_798066) baseStart_798066 baseEnd_798066 := by
    simpa [prefixWord, tailWord_798066, baseEnd_798066] using wordTrace_append hprefix tailTrace_798066
  have hstable : (prefixWord ++ tailWord_798066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798066).length < 2 ^ (prefixWord ++ tailWord_798066).sum := by decide
  have hdescent : baseEnd_798066 < baseStart_798066 := by decide
  rcases family_descends (prefixWord ++ tailWord_798066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798073 : List Nat := [1, 2, 1, 3, 2, 1, 2, 2, 2, 5, 2]
def baseStart_798073 : Nat := 118140960795 + 798073 * 2 ^ 59
def prefixEnd_798073 : Nat := 4983230072969 + 3 ^ 40 * 798073 * 2
def baseEnd_798073 : Nat := 409795046375761269417235

theorem tailTrace_798073 : CollatzResearch.WordTrace tailWord_798073 prefixEnd_798073 409795046375761269417235 := by
  unfold tailWord_798073
  simp only [CollatzResearch.WordTrace]
  refine ⟨29108113637725295862110873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19405409091816863908073915 29108113637725295862110873)
  ·
    refine ⟨21831085228293971896583155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29108113637725295862110873 21831085228293971896583155)
    ·
      refine ⟨32746627842440957844874733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21831085228293971896583155 32746627842440957844874733)
      ·
        refine ⟨12279985440915359191828025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32746627842440957844874733 12279985440915359191828025)
        ·
          refine ⟨9209989080686519393871019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12279985440915359191828025 9209989080686519393871019)
          ·
            refine ⟨13814983621029779090806529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9209989080686519393871019 13814983621029779090806529)
            ·
              refine ⟨10361237715772334318104897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13814983621029779090806529 10361237715772334318104897)
              ·
                refine ⟨7770928286829250738578673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10361237715772334318104897 7770928286829250738578673)
                ·
                  refine ⟨5828196215121938053934005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7770928286829250738578673 5828196215121938053934005)
                  ·
                    refine ⟨546393395167681692556313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5828196215121938053934005 546393395167681692556313)
                    ·
                      refine ⟨409795046375761269417235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 546393395167681692556313 409795046375761269417235)
                      ·
                        rfl

theorem cell23_798073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 5, 2].length) (baseStart_798073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_798073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_798073 prefixEnd_798073 := by exact prefixLift 798073
  have htrace : WordTrace (prefixWord ++ tailWord_798073) baseStart_798073 baseEnd_798073 := by
    simpa [prefixWord, tailWord_798073, baseEnd_798073] using wordTrace_append hprefix tailTrace_798073
  have hstable : (prefixWord ++ tailWord_798073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798073).length < 2 ^ (prefixWord ++ tailWord_798073).sum := by decide
  have hdescent : baseEnd_798073 < baseStart_798073 := by decide
  rcases family_descends (prefixWord ++ tailWord_798073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798100 : List Nat := [2, 4, 2, 1, 2, 2, 1, 2, 2, 5]
def baseStart_798100 : Nat := 118140960795 + 798100 * 2 ^ 59
def prefixEnd_798100 : Nat := 4983230072969 + 3 ^ 40 * 798100 * 2
def baseEnd_798100 : Nat := 136602970117810887926537

theorem tailTrace_798100 : CollatzResearch.WordTrace tailWord_798100 prefixEnd_798100 136602970117810887926537 := by
  unfold tailWord_798100
  simp only [CollatzResearch.WordTrace]
  refine ⟨14554549204313739736671877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19406065605751652982229169 14554549204313739736671877)
  ·
    refine ⟨2728977975808826200625977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14554549204313739736671877 2728977975808826200625977)
    ·
      refine ⟨2046733481856619650469483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2728977975808826200625977 2046733481856619650469483)
      ·
        refine ⟨3070100222784929475704225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2046733481856619650469483 3070100222784929475704225)
        ·
          refine ⟨2302575167088697106778169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3070100222784929475704225 2302575167088697106778169)
          ·
            refine ⟨1726931375316522830083627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2302575167088697106778169 1726931375316522830083627)
            ·
              refine ⟨2590397062974784245125441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1726931375316522830083627 2590397062974784245125441)
              ·
                refine ⟨1942797797231088183844081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2590397062974784245125441 1942797797231088183844081)
                ·
                  refine ⟨1457098347923316137883061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1942797797231088183844081 1457098347923316137883061)
                  ·
                    refine ⟨136602970117810887926537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1457098347923316137883061 136602970117810887926537)
                    ·
                      rfl

theorem cell23_798100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_798100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_798100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_798100 prefixEnd_798100 := by exact prefixLift 798100
  have htrace : WordTrace (prefixWord ++ tailWord_798100) baseStart_798100 baseEnd_798100 := by
    simpa [prefixWord, tailWord_798100, baseEnd_798100] using wordTrace_append hprefix tailTrace_798100
  have hstable : (prefixWord ++ tailWord_798100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798100).length < 2 ^ (prefixWord ++ tailWord_798100).sum := by decide
  have hdescent : baseEnd_798100 < baseStart_798100 := by decide
  rcases family_descends (prefixWord ++ tailWord_798100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798164 : List Nat := [2, 4, 1, 2, 3, 1, 1, 4, 1, 4]
def baseStart_798164 : Nat := 118140960795 + 798164 * 2 ^ 59
def prefixEnd_798164 : Nat := 4983230072969 + 3 ^ 40 * 798164 * 2
def baseEnd_798164 : Nat := 136613924371773471126439

theorem tailTrace_798164 : CollatzResearch.WordTrace tailWord_798164 prefixEnd_798164 136613924371773471126439 := by
  unfold tailWord_798164
  simp only [CollatzResearch.WordTrace]
  refine ⟨14555716340197809201836773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19407621786930412269115697 14555716340197809201836773)
  ·
    refine ⟨2729196813787089225344395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14555716340197809201836773 2729196813787089225344395)
    ·
      refine ⟨4093795220680633838016593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2729196813787089225344395 4093795220680633838016593)
      ·
        refine ⟨3070346415510475378512445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4093795220680633838016593 3070346415510475378512445)
        ·
          refine ⟨1151379905816428266942167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3070346415510475378512445 1151379905816428266942167)
          ·
            refine ⟨1727069858724642400413251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1151379905816428266942167 1727069858724642400413251)
            ·
              refine ⟨2590604788086963600619877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1727069858724642400413251 2590604788086963600619877)
              ·
                refine ⟨485738397766305675116227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2590604788086963600619877 485738397766305675116227)
                ·
                  refine ⟨728607596649458512674341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 485738397766305675116227 728607596649458512674341)
                  ·
                    refine ⟨136613924371773471126439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 728607596649458512674341 136613924371773471126439)
                    ·
                      rfl

theorem cell23_798164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 4, 1, 4].length) (baseStart_798164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_798164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_798164 prefixEnd_798164 := by exact prefixLift 798164
  have htrace : WordTrace (prefixWord ++ tailWord_798164) baseStart_798164 baseEnd_798164 := by
    simpa [prefixWord, tailWord_798164, baseEnd_798164] using wordTrace_append hprefix tailTrace_798164
  have hstable : (prefixWord ++ tailWord_798164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798164).length < 2 ^ (prefixWord ++ tailWord_798164).sum := by decide
  have hdescent : baseEnd_798164 < baseStart_798164 := by decide
  rcases family_descends (prefixWord ++ tailWord_798164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798180 : List Nat := [2, 3, 1, 1, 1, 1, 1, 4, 4, 3, 2]
def baseStart_798180 : Nat := 118140960795 + 798180 * 2 ^ 59
def prefixEnd_798180 : Nat := 4983230072969 + 3 ^ 40 * 798180 * 2
def baseEnd_798180 : Nat := 409849988805792350779243

theorem tailTrace_798180 : CollatzResearch.WordTrace tailWord_798180 prefixEnd_798180 409849988805792350779243 := by
  unfold tailWord_798180
  simp only [CollatzResearch.WordTrace]
  refine ⟨14556008124168826568127997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19408010832225102090837329 14556008124168826568127997)
  ·
    refine ⟨5458503046563309963047999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14556008124168826568127997 5458503046563309963047999)
    ·
      refine ⟨8187754569844964944571999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5458503046563309963047999 8187754569844964944571999)
      ·
        refine ⟨12281631854767447416857999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8187754569844964944571999 12281631854767447416857999)
        ·
          refine ⟨18422447782151171125286999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12281631854767447416857999 18422447782151171125286999)
          ·
            refine ⟨27633671673226756687930499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18422447782151171125286999 27633671673226756687930499)
            ·
              refine ⟨41450507509840135031895749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27633671673226756687930499 41450507509840135031895749)
              ·
                refine ⟨7771970158095025318480453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41450507509840135031895749 7771970158095025318480453)
                ·
                  refine ⟨1457244404642817247215085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7771970158095025318480453 1457244404642817247215085)
                  ·
                    refine ⟨546466651741056467705657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1457244404642817247215085 546466651741056467705657)
                    ·
                      refine ⟨409849988805792350779243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 546466651741056467705657 409849988805792350779243)
                      ·
                        rfl

theorem cell23_798180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 4, 3, 2].length) (baseStart_798180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_798180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_798180 prefixEnd_798180 := by exact prefixLift 798180
  have htrace : WordTrace (prefixWord ++ tailWord_798180) baseStart_798180 baseEnd_798180 := by
    simpa [prefixWord, tailWord_798180, baseEnd_798180] using wordTrace_append hprefix tailTrace_798180
  have hstable : (prefixWord ++ tailWord_798180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798180).length < 2 ^ (prefixWord ++ tailWord_798180).sum := by decide
  have hdescent : baseEnd_798180 < baseStart_798180 := by decide
  rcases family_descends (prefixWord ++ tailWord_798180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798190 : List Nat := [4, 1, 2, 1, 2, 1, 2, 4, 1, 5]
def baseStart_798190 : Nat := 118140960795 + 798190 * 2 ^ 59
def prefixEnd_798190 : Nat := 4983230072969 + 3 ^ 40 * 798190 * 2
def baseEnd_798190 : Nat := 136618374537445770551399

theorem tailTrace_798190 : CollatzResearch.WordTrace tailWord_798190 prefixEnd_798190 136618374537445770551399 := by
  unfold tailWord_798190
  simp only [CollatzResearch.WordTrace]
  refine ⟨3639047622287678105515003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19408253985534283229413349 3639047622287678105515003)
  ·
    refine ⟨5458571433431517158272505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3639047622287678105515003 5458571433431517158272505)
    ·
      refine ⟨4093928575073637868704379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5458571433431517158272505 4093928575073637868704379)
      ·
        refine ⟨6140892862610456803056569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4093928575073637868704379 6140892862610456803056569)
        ·
          refine ⟨4605669646957842602292427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6140892862610456803056569 4605669646957842602292427)
          ·
            refine ⟨6908504470436763903438641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4605669646957842602292427 6908504470436763903438641)
            ·
              refine ⟨5181378352827572927578981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6908504470436763903438641 5181378352827572927578981)
              ·
                refine ⟨971508441155169923921059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5181378352827572927578981 971508441155169923921059)
                ·
                  refine ⟨1457262661732754885881589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 971508441155169923921059 1457262661732754885881589)
                  ·
                    refine ⟨136618374537445770551399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1457262661732754885881589 136618374537445770551399)
                    ·
                      rfl

theorem cell23_798190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_798190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_798190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_798190 prefixEnd_798190 := by exact prefixLift 798190
  have htrace : WordTrace (prefixWord ++ tailWord_798190) baseStart_798190 baseEnd_798190 := by
    simpa [prefixWord, tailWord_798190, baseEnd_798190] using wordTrace_append hprefix tailTrace_798190
  have hstable : (prefixWord ++ tailWord_798190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798190).length < 2 ^ (prefixWord ++ tailWord_798190).sum := by decide
  have hdescent : baseEnd_798190 < baseStart_798190 := by decide
  rcases family_descends (prefixWord ++ tailWord_798190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798203 : List Nat := [1, 1, 1, 1, 1, 3, 2, 3, 6, 4]
def baseStart_798203 : Nat := 118140960795 + 798203 * 2 ^ 59
def prefixEnd_798203 : Nat := 4983230072969 + 3 ^ 40 * 798203 * 2
def baseEnd_798203 : Nat := 136620599620281920263879

theorem tailTrace_798203 : CollatzResearch.WordTrace tailWord_798203 prefixEnd_798203 136620599620281920263879 := by
  unfold tailWord_798203
  simp only [CollatzResearch.WordTrace]
  refine ⟨29112855127254328064343263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19408570084836218709562175 29112855127254328064343263)
  ·
    refine ⟨43669282690881492096514895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29112855127254328064343263 43669282690881492096514895)
    ·
      refine ⟨65503924036322238144772343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43669282690881492096514895 65503924036322238144772343)
      ·
        refine ⟨98255886054483357217158515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65503924036322238144772343 98255886054483357217158515)
        ·
          refine ⟨147383829081725035825737773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98255886054483357217158515 147383829081725035825737773)
          ·
            refine ⟨55268935905646888434651665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147383829081725035825737773 55268935905646888434651665)
            ·
              refine ⟨41451701929235166325988749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55268935905646888434651665 41451701929235166325988749)
              ·
                refine ⟨15544388223463187372245781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41451701929235166325988749 15544388223463187372245781)
                ·
                  refine ⟨728643197974836908074021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 15544388223463187372245781 728643197974836908074021)
                  ·
                    refine ⟨136620599620281920263879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 728643197974836908074021 136620599620281920263879)
                    ·
                      rfl

theorem cell23_798203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 6, 4].length) (baseStart_798203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_798203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_798203 prefixEnd_798203 := by exact prefixLift 798203
  have htrace : WordTrace (prefixWord ++ tailWord_798203) baseStart_798203 baseEnd_798203 := by
    simpa [prefixWord, tailWord_798203, baseEnd_798203] using wordTrace_append hprefix tailTrace_798203
  have hstable : (prefixWord ++ tailWord_798203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798203).length < 2 ^ (prefixWord ++ tailWord_798203).sum := by decide
  have hdescent : baseEnd_798203 < baseStart_798203 := by decide
  rcases family_descends (prefixWord ++ tailWord_798203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798213 : List Nat := [1, 3, 1, 1, 2, 2, 1, 5, 1, 1, 5]
def baseStart_798213 : Nat := 118140960795 + 798213 * 2 ^ 59
def prefixEnd_798213 : Nat := 4983230072969 + 3 ^ 40 * 798213 * 2
def baseEnd_798213 : Nat := 409866933667390721666591

theorem tailTrace_798213 : CollatzResearch.WordTrace tailWord_798213 prefixEnd_798213 409866933667390721666591 := by
  unfold tailWord_798213
  simp only [CollatzResearch.WordTrace]
  refine ⟨29113219857218099772207293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19408813238145399848138195 29113219857218099772207293)
  ·
    refine ⟨10917457446456787414577735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29113219857218099772207293 10917457446456787414577735)
    ·
      refine ⟨16376186169685181121866603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10917457446456787414577735 16376186169685181121866603)
      ·
        refine ⟨24564279254527771682799905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16376186169685181121866603 24564279254527771682799905)
        ·
          refine ⟨18423209440895828762099929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24564279254527771682799905 18423209440895828762099929)
          ·
            refine ⟨13817407080671871571574947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18423209440895828762099929 13817407080671871571574947)
            ·
              refine ⟨20726110621007807357362421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13817407080671871571574947 20726110621007807357362421)
              ·
                refine ⟨1943072870719481939752727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20726110621007807357362421 1943072870719481939752727)
                ·
                  refine ⟨2914609306079222909629091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1943072870719481939752727 2914609306079222909629091)
                  ·
                    refine ⟨4371913959118834364443637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2914609306079222909629091 4371913959118834364443637)
                    ·
                      refine ⟨409866933667390721666591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4371913959118834364443637 409866933667390721666591)
                      ·
                        rfl

theorem cell23_798213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 5, 1, 1, 5].length) (baseStart_798213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_798213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_798213 prefixEnd_798213 := by exact prefixLift 798213
  have htrace : WordTrace (prefixWord ++ tailWord_798213) baseStart_798213 baseEnd_798213 := by
    simpa [prefixWord, tailWord_798213, baseEnd_798213] using wordTrace_append hprefix tailTrace_798213
  have hstable : (prefixWord ++ tailWord_798213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798213).length < 2 ^ (prefixWord ++ tailWord_798213).sum := by decide
  have hdescent : baseEnd_798213 < baseStart_798213 := by decide
  rcases family_descends (prefixWord ++ tailWord_798213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798227 : List Nat := [1, 1, 1, 2, 1, 6, 1, 3, 3, 2, 2]
def baseStart_798227 : Nat := 118140960795 + 798227 * 2 ^ 59
def prefixEnd_798227 : Nat := 4983230072969 + 3 ^ 40 * 798227 * 2
def baseEnd_798227 : Nat := 409874122396553666891527

theorem tailTrace_798227 : CollatzResearch.WordTrace tailWord_798227 prefixEnd_798227 409874122396553666891527 := by
  unfold tailWord_798227
  simp only [CollatzResearch.WordTrace]
  refine ⟨29113730479167380163216935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19409153652778253442144623 29113730479167380163216935)
  ·
    refine ⟨43670595718751070244825403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29113730479167380163216935 43670595718751070244825403)
    ·
      refine ⟨65505893578126605367238105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43670595718751070244825403 65505893578126605367238105)
      ·
        refine ⟨49129420183594954025428579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65505893578126605367238105 49129420183594954025428579)
        ·
          refine ⟨73694130275392431038142869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49129420183594954025428579 73694130275392431038142869)
          ·
            refine ⟨3454412356659020204912947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 73694130275392431038142869 3454412356659020204912947)
            ·
              refine ⟨5181618534988530307369421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3454412356659020204912947 5181618534988530307369421)
              ·
                refine ⟨1943106950620698865263533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5181618534988530307369421 1943106950620698865263533)
                ·
                  refine ⟨728665106482762074473825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1943106950620698865263533 728665106482762074473825)
                  ·
                    refine ⟨546498829862071555855369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 728665106482762074473825 546498829862071555855369)
                    ·
                      refine ⟨409874122396553666891527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 546498829862071555855369 409874122396553666891527)
                      ·
                        rfl

theorem cell23_798227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 3, 3, 2, 2].length) (baseStart_798227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_798227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_798227 prefixEnd_798227 := by exact prefixLift 798227
  have htrace : WordTrace (prefixWord ++ tailWord_798227) baseStart_798227 baseEnd_798227 := by
    simpa [prefixWord, tailWord_798227, baseEnd_798227] using wordTrace_append hprefix tailTrace_798227
  have hstable : (prefixWord ++ tailWord_798227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798227).length < 2 ^ (prefixWord ++ tailWord_798227).sum := by decide
  have hdescent : baseEnd_798227 < baseStart_798227 := by decide
  rcases family_descends (prefixWord ++ tailWord_798227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798240 : List Nat := [2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 6]
def baseStart_798240 : Nat := 118140960795 + 798240 * 2 ^ 59
def prefixEnd_798240 : Nat := 4983230072969 + 3 ^ 40 * 798240 * 2
def baseEnd_798240 : Nat := 409880797645062116028967

theorem tailTrace_798240 : CollatzResearch.WordTrace tailWord_798240 prefixEnd_798240 409880797645062116028967 := by
  unfold tailWord_798240
  simp only [CollatzResearch.WordTrace]
  refine ⟨14557102314060141691720087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19409469752080188922293449 14557102314060141691720087)
  ·
    refine ⟨21835653471090212537580131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14557102314060141691720087 21835653471090212537580131)
    ·
      refine ⟨32753480206635318806370197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21835653471090212537580131 32753480206635318806370197)
      ·
        refine ⟨1535319384686030569048603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 32753480206635318806370197 1535319384686030569048603)
        ·
          refine ⟨2302979077029045853572905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1535319384686030569048603 2302979077029045853572905)
          ·
            refine ⟨1727234307771784390179679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2302979077029045853572905 1727234307771784390179679)
            ·
              refine ⟨2590851461657676585269519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1727234307771784390179679 2590851461657676585269519)
              ·
                refine ⟨3886277192486514877904279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2590851461657676585269519 3886277192486514877904279)
                ·
                  refine ⟨5829415788729772316856419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3886277192486514877904279 5829415788729772316856419)
                  ·
                    refine ⟨8744123683094658475284629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5829415788729772316856419 8744123683094658475284629)
                    ·
                      refine ⟨409880797645062116028967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8744123683094658475284629 409880797645062116028967)
                      ·
                        rfl

theorem cell23_798240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_798240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_798240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_798240 prefixEnd_798240 := by exact prefixLift 798240
  have htrace : WordTrace (prefixWord ++ tailWord_798240) baseStart_798240 baseEnd_798240 := by
    simpa [prefixWord, tailWord_798240, baseEnd_798240] using wordTrace_append hprefix tailTrace_798240
  have hstable : (prefixWord ++ tailWord_798240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798240).length < 2 ^ (prefixWord ++ tailWord_798240).sum := by decide
  have hdescent : baseEnd_798240 < baseStart_798240 := by decide
  rcases family_descends (prefixWord ++ tailWord_798240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798261 : List Nat := [1, 3, 3, 1, 1, 3, 3, 3, 1, 2, 2]
def baseStart_798261 : Nat := 118140960795 + 798261 * 2 ^ 59
def prefixEnd_798261 : Nat := 4983230072969 + 3 ^ 40 * 798261 * 2
def baseEnd_798261 : Nat := 409891580738806533866371

theorem tailTrace_798261 : CollatzResearch.WordTrace tailWord_798261 prefixEnd_798261 409891580738806533866371 := by
  unfold tailWord_798261
  simp only [CollatzResearch.WordTrace]
  refine ⟨29114970561044203969954637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19409980374029469313303091 29114970561044203969954637)
  ·
    refine ⟨10918113960391576488732989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29114970561044203969954637 10918113960391576488732989)
    ·
      refine ⟨4094292735146841183274871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10918113960391576488732989 4094292735146841183274871)
      ·
        refine ⟨6141439102720261774912307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4094292735146841183274871 6141439102720261774912307)
        ·
          refine ⟨9212158654080392662368461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6141439102720261774912307 9212158654080392662368461)
          ·
            refine ⟨3454559495280147248388173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9212158654080392662368461 3454559495280147248388173)
            ·
              refine ⟨1295459810730055218145565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3454559495280147248388173 1295459810730055218145565)
              ·
                refine ⟨485797429023770706804587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1295459810730055218145565 485797429023770706804587)
                ·
                  refine ⟨728696143535656060206881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 485797429023770706804587 728696143535656060206881)
                  ·
                    refine ⟨546522107651742045155161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 728696143535656060206881 546522107651742045155161)
                    ·
                      refine ⟨409891580738806533866371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 546522107651742045155161 409891580738806533866371)
                      ·
                        rfl

theorem cell23_798261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 3, 1, 2, 2].length) (baseStart_798261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_798261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_798261 prefixEnd_798261 := by exact prefixLift 798261
  have htrace : WordTrace (prefixWord ++ tailWord_798261) baseStart_798261 baseEnd_798261 := by
    simpa [prefixWord, tailWord_798261, baseEnd_798261] using wordTrace_append hprefix tailTrace_798261
  have hstable : (prefixWord ++ tailWord_798261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798261).length < 2 ^ (prefixWord ++ tailWord_798261).sum := by decide
  have hdescent : baseEnd_798261 < baseStart_798261 := by decide
  rcases family_descends (prefixWord ++ tailWord_798261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798277 : List Nat := [1, 3, 1, 1, 1, 4, 2, 4, 2, 1, 3]
def baseStart_798277 : Nat := 118140960795 + 798277 * 2 ^ 59
def prefixEnd_798277 : Nat := 4983230072969 + 3 ^ 40 * 798277 * 2
def baseEnd_798277 : Nat := 409899796429278471266297

theorem tailTrace_798277 : CollatzResearch.WordTrace tailWord_798277 prefixEnd_798277 409899796429278471266297 := by
  unfold tailWord_798277
  simp only [CollatzResearch.WordTrace]
  refine ⟨29115554128986238702537085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19410369419324159135024723 29115554128986238702537085)
  ·
    refine ⟨10918332798369839513451407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29115554128986238702537085 10918332798369839513451407)
    ·
      refine ⟨16377499197554759270177111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10918332798369839513451407 16377499197554759270177111)
      ·
        refine ⟨24566248796332138905265667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16377499197554759270177111 24566248796332138905265667)
        ·
          refine ⟨36849373194498208357898501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24566248796332138905265667 36849373194498208357898501)
          ·
            refine ⟨6909257473968414067105969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36849373194498208357898501 6909257473968414067105969)
            ·
              refine ⟨5181943105476310550329477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6909257473968414067105969 5181943105476310550329477)
              ·
                refine ⟨971614332276808228186777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5181943105476310550329477 971614332276808228186777)
                ·
                  refine ⟨728710749207606171140083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 971614332276808228186777 728710749207606171140083)
                  ·
                    refine ⟨1093066123811409256710125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 728710749207606171140083 1093066123811409256710125)
                    ·
                      refine ⟨409899796429278471266297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1093066123811409256710125 409899796429278471266297)
                      ·
                        rfl

theorem cell23_798277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 4, 2, 1, 3].length) (baseStart_798277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_798277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_798277 prefixEnd_798277 := by exact prefixLift 798277
  have htrace : WordTrace (prefixWord ++ tailWord_798277) baseStart_798277 baseEnd_798277 := by
    simpa [prefixWord, tailWord_798277, baseEnd_798277] using wordTrace_append hprefix tailTrace_798277
  have hstable : (prefixWord ++ tailWord_798277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798277).length < 2 ^ (prefixWord ++ tailWord_798277).sum := by decide
  have hdescent : baseEnd_798277 < baseStart_798277 := by decide
  rcases family_descends (prefixWord ++ tailWord_798277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798283 : List Nat := [1, 1, 1, 1, 3, 1, 3, 3, 2, 3, 4]
def baseStart_798283 : Nat := 118140960795 + 798283 * 2 ^ 59
def prefixEnd_798283 : Nat := 4983230072969 + 3 ^ 40 * 798283 * 2
def baseEnd_798283 : Nat := 409902877313205447791269

theorem tailTrace_798283 : CollatzResearch.WordTrace tailWord_798283 prefixEnd_798283 409902877313205447791269 := by
  unfold tailWord_798283
  simp only [CollatzResearch.WordTrace]
  refine ⟨29115772966964501727255503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19410515311309667818170335 29115772966964501727255503)
  ·
    refine ⟨43673659450446752590883255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29115772966964501727255503 43673659450446752590883255)
    ·
      refine ⟨65510489175670128886324883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43673659450446752590883255 65510489175670128886324883)
      ·
        refine ⟨98265733763505193329487325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65510489175670128886324883 98265733763505193329487325)
        ·
          refine ⟨36849650161314447498557747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98265733763505193329487325 36849650161314447498557747)
          ·
            refine ⟨55274475241971671247836621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36849650161314447498557747 55274475241971671247836621)
            ·
              refine ⟨20727928215739376717938733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55274475241971671247836621 20727928215739376717938733)
              ·
                refine ⟨7772973080902266269227025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20727928215739376717938733 7772973080902266269227025)
                ·
                  refine ⟨5829729810676699701920269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7772973080902266269227025 5829729810676699701920269)
                  ·
                    refine ⟨2186148679003762388220101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5829729810676699701920269 2186148679003762388220101)
                    ·
                      refine ⟨409902877313205447791269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2186148679003762388220101 409902877313205447791269)
                      ·
                        rfl

theorem cell23_798283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 3, 4].length) (baseStart_798283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_798283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_798283 prefixEnd_798283 := by exact prefixLift 798283
  have htrace : WordTrace (prefixWord ++ tailWord_798283) baseStart_798283 baseEnd_798283 := by
    simpa [prefixWord, tailWord_798283, baseEnd_798283] using wordTrace_append hprefix tailTrace_798283
  have hstable : (prefixWord ++ tailWord_798283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798283).length < 2 ^ (prefixWord ++ tailWord_798283).sum := by decide
  have hdescent : baseEnd_798283 < baseStart_798283 := by decide
  rcases family_descends (prefixWord ++ tailWord_798283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798293 : List Nat := [1, 3, 2, 2, 1, 1, 1, 3, 1, 8]
def baseStart_798293 : Nat := 118140960795 + 798293 * 2 ^ 59
def prefixEnd_798293 : Nat := 4983230072969 + 3 ^ 40 * 798293 * 2
def baseEnd_798293 : Nat := 136636004039916802888741

theorem tailTrace_798293 : CollatzResearch.WordTrace tailWord_798293 prefixEnd_798293 136636004039916802888741 := by
  unfold tailWord_798293
  simp only [CollatzResearch.WordTrace]
  refine ⟨29116137696928273435119533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19410758464618848956746355 29116137696928273435119533)
  ·
    refine ⟨10918551636348102538169825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29116137696928273435119533 10918551636348102538169825)
    ·
      refine ⟨8188913727261076903627369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10918551636348102538169825 8188913727261076903627369)
      ·
        refine ⟨6141685295445807677720527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8188913727261076903627369 6141685295445807677720527)
        ·
          refine ⟨9212527943168711516580791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6141685295445807677720527 9212527943168711516580791)
          ·
            refine ⟨13818791914753067274871187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9212527943168711516580791 13818791914753067274871187)
            ·
              refine ⟨20728187872129600912306781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13818791914753067274871187 20728187872129600912306781)
              ·
                refine ⟨7773070452048600342115043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20728187872129600912306781 7773070452048600342115043)
                ·
                  refine ⟨11659605678072900513172565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7773070452048600342115043 11659605678072900513172565)
                  ·
                    refine ⟨136636004039916802888741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 11659605678072900513172565 136636004039916802888741)
                    ·
                      rfl

theorem cell23_798293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 8].length) (baseStart_798293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_798293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_798293 prefixEnd_798293 := by exact prefixLift 798293
  have htrace : WordTrace (prefixWord ++ tailWord_798293) baseStart_798293 baseEnd_798293 := by
    simpa [prefixWord, tailWord_798293, baseEnd_798293] using wordTrace_append hprefix tailTrace_798293
  have hstable : (prefixWord ++ tailWord_798293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798293).length < 2 ^ (prefixWord ++ tailWord_798293).sum := by decide
  have hdescent : baseEnd_798293 < baseStart_798293 := by decide
  rcases family_descends (prefixWord ++ tailWord_798293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798320 : List Nat := [2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 5]
def baseStart_798320 : Nat := 118140960795 + 798320 * 2 ^ 59
def prefixEnd_798320 : Nat := 4983230072969 + 3 ^ 40 * 798320 * 2
def baseEnd_798320 : Nat := 409921876097421803028599

theorem tailTrace_798320 : CollatzResearch.WordTrace tailWord_798320 prefixEnd_798320 409921876097421803028599 := by
  unfold tailWord_798320
  simp only [CollatzResearch.WordTrace]
  refine ⟨14558561233915228523176207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19411414978553638030901609 14558561233915228523176207)
  ·
    refine ⟨21837841850872842784764311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14558561233915228523176207 21837841850872842784764311)
    ·
      refine ⟨32756762776309264177146467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21837841850872842784764311 32756762776309264177146467)
      ·
        refine ⟨49135144164463896265719701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32756762776309264177146467 49135144164463896265719701)
        ·
          refine ⟨2303209882709245137455611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 49135144164463896265719701 2303209882709245137455611)
          ·
            refine ⟨3454814824063867706183417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2303209882709245137455611 3454814824063867706183417)
            ·
              refine ⟨2591111118047900779637563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3454814824063867706183417 2591111118047900779637563)
              ·
                refine ⟨3886666677071851169456345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2591111118047900779637563 3886666677071851169456345)
                ·
                  refine ⟨2915000007803888377092259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3886666677071851169456345 2915000007803888377092259)
                  ·
                    refine ⟨4372500011705832565638389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2915000007803888377092259 4372500011705832565638389)
                    ·
                      refine ⟨409921876097421803028599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4372500011705832565638389 409921876097421803028599)
                      ·
                        rfl

theorem cell23_798320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 5].length) (baseStart_798320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_798320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_798320 prefixEnd_798320 := by exact prefixLift 798320
  have htrace : WordTrace (prefixWord ++ tailWord_798320) baseStart_798320 baseEnd_798320 := by
    simpa [prefixWord, tailWord_798320, baseEnd_798320] using wordTrace_append hprefix tailTrace_798320
  have hstable : (prefixWord ++ tailWord_798320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798320).length < 2 ^ (prefixWord ++ tailWord_798320).sum := by decide
  have hdescent : baseEnd_798320 < baseStart_798320 := by decide
  rcases family_descends (prefixWord ++ tailWord_798320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798402 : List Nat := [3, 5, 1, 2, 2, 1, 1, 1, 1, 4, 2]
def baseStart_798402 : Nat := 118140960795 + 798402 * 2 ^ 59
def prefixEnd_798402 : Nat := 4983230072969 + 3 ^ 40 * 798402 * 2
def baseEnd_798402 : Nat := 409963981511090482203223

theorem tailTrace_798402 : CollatzResearch.WordTrace tailWord_798402 prefixEnd_798402 409963981511090482203223 := by
  unfold tailWord_798402
  simp only [CollatzResearch.WordTrace]
  refine ⟨7280028313383346262709365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19413408835688923367224973 7280028313383346262709365)
  ·
    refine ⟨682502654379688712129003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7280028313383346262709365 682502654379688712129003)
    ·
      refine ⟨1023753981569533068193505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 682502654379688712129003 1023753981569533068193505)
      ·
        refine ⟨767815486177149801145129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1023753981569533068193505 767815486177149801145129)
        ·
          refine ⟨575861614632862350858847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 767815486177149801145129 575861614632862350858847)
          ·
            refine ⟨863792421949293526288271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 575861614632862350858847 863792421949293526288271)
            ·
              refine ⟨1295688632923940289432407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 863792421949293526288271 1295688632923940289432407)
              ·
                refine ⟨1943532949385910434148611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1295688632923940289432407 1943532949385910434148611)
                ·
                  refine ⟨2915299424078865651222917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1943532949385910434148611 2915299424078865651222917)
                  ·
                    refine ⟨546618642014787309604297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2915299424078865651222917 546618642014787309604297)
                    ·
                      refine ⟨409963981511090482203223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 546618642014787309604297 409963981511090482203223)
                      ·
                        rfl

theorem cell23_798402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_798402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_798402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_798402 prefixEnd_798402 := by exact prefixLift 798402
  have htrace : WordTrace (prefixWord ++ tailWord_798402) baseStart_798402 baseEnd_798402 := by
    simpa [prefixWord, tailWord_798402, baseEnd_798402] using wordTrace_append hprefix tailTrace_798402
  have hstable : (prefixWord ++ tailWord_798402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798402).length < 2 ^ (prefixWord ++ tailWord_798402).sum := by decide
  have hdescent : baseEnd_798402 < baseStart_798402 := by decide
  rcases family_descends (prefixWord ++ tailWord_798402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798407 : List Nat := [1, 1, 4, 1, 1, 1, 3, 3, 2, 4, 2]
def baseStart_798407 : Nat := 118140960795 + 798407 * 2 ^ 59
def prefixEnd_798407 : Nat := 4983230072969 + 3 ^ 40 * 798407 * 2
def baseEnd_798407 : Nat := 409966548914362962640699

theorem tailTrace_798407 : CollatzResearch.WordTrace tailWord_798407 prefixEnd_798407 409966548914362962640699 := by
  unfold tailWord_798407
  simp only [CollatzResearch.WordTrace]
  refine ⟨29120295618515270904769475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19413530412343513936512983 29120295618515270904769475)
  ·
    refine ⟨43680443427772906357154213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29120295618515270904769475 43680443427772906357154213)
    ·
      refine ⟨8190083142707419941966415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43680443427772906357154213 8190083142707419941966415)
      ·
        refine ⟨12285124714061129912949623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8190083142707419941966415 12285124714061129912949623)
        ·
          refine ⟨18427687071091694869424435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12285124714061129912949623 18427687071091694869424435)
          ·
            refine ⟨27641530606637542304136653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18427687071091694869424435 27641530606637542304136653)
            ·
              refine ⟨10365573977489078364051245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27641530606637542304136653 10365573977489078364051245)
              ·
                refine ⟨3887090241558404386519217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10365573977489078364051245 3887090241558404386519217)
                ·
                  refine ⟨2915317681168803289889413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3887090241558404386519217 2915317681168803289889413)
                  ·
                    refine ⟨546622065219150616854265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2915317681168803289889413 546622065219150616854265)
                    ·
                      refine ⟨409966548914362962640699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 546622065219150616854265 409966548914362962640699)
                      ·
                        rfl

theorem cell23_798407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 2, 4, 2].length) (baseStart_798407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_798407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_798407 prefixEnd_798407 := by exact prefixLift 798407
  have htrace : WordTrace (prefixWord ++ tailWord_798407) baseStart_798407 baseEnd_798407 := by
    simpa [prefixWord, tailWord_798407, baseEnd_798407] using wordTrace_append hprefix tailTrace_798407
  have hstable : (prefixWord ++ tailWord_798407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798407).length < 2 ^ (prefixWord ++ tailWord_798407).sum := by decide
  have hdescent : baseEnd_798407 < baseStart_798407 := by decide
  rcases family_descends (prefixWord ++ tailWord_798407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798417 : List Nat := [1, 2, 2, 1, 2, 4, 2, 2, 3, 4]
def baseStart_798417 : Nat := 118140960795 + 798417 * 2 ^ 59
def prefixEnd_798417 : Nat := 4983230072969 + 3 ^ 40 * 798417 * 2
def baseEnd_798417 : Nat := 136657227906969307838551

theorem tailTrace_798417 : CollatzResearch.WordTrace tailWord_798417 prefixEnd_798417 136657227906969307838551 := by
  unfold tailWord_798417
  simp only [CollatzResearch.WordTrace]
  refine ⟨29120660348479042612633505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19413773565652695075089003 29120660348479042612633505)
  ·
    refine ⟨21840495261359281959475129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29120660348479042612633505 21840495261359281959475129)
    ·
      refine ⟨16380371446019461469606347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21840495261359281959475129 16380371446019461469606347)
      ·
        refine ⟨24570557169029192204409521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16380371446019461469606347 24570557169029192204409521)
        ·
          refine ⟨18427917876771894153307141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24570557169029192204409521 18427917876771894153307141)
          ·
            refine ⟨3455234601894730153745089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18427917876771894153307141 3455234601894730153745089)
            ·
              refine ⟨2591425951421047615308817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3455234601894730153745089 2591425951421047615308817)
              ·
                refine ⟨1943569463565785711481613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2591425951421047615308817 1943569463565785711481613)
                ·
                  refine ⟨728838548837169641805605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1943569463565785711481613 728838548837169641805605)
                  ·
                    refine ⟨136657227906969307838551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 728838548837169641805605 136657227906969307838551)
                    ·
                      rfl

theorem cell23_798417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 2, 3, 4].length) (baseStart_798417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_798417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_798417 prefixEnd_798417 := by exact prefixLift 798417
  have htrace : WordTrace (prefixWord ++ tailWord_798417) baseStart_798417 baseEnd_798417 := by
    simpa [prefixWord, tailWord_798417, baseEnd_798417] using wordTrace_append hprefix tailTrace_798417
  have hstable : (prefixWord ++ tailWord_798417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798417).length < 2 ^ (prefixWord ++ tailWord_798417).sum := by decide
  have hdescent : baseEnd_798417 < baseStart_798417 := by decide
  rcases family_descends (prefixWord ++ tailWord_798417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798467 : List Nat := [1, 1, 1, 3, 2, 2, 2, 1, 3, 5, 2]
def baseStart_798467 : Nat := 118140960795 + 798467 * 2 ^ 59
def prefixEnd_798467 : Nat := 4983230072969 + 3 ^ 40 * 798467 * 2
def baseEnd_798467 : Nat := 409997357753632727890423

theorem tailTrace_798467 : CollatzResearch.WordTrace tailWord_798467 prefixEnd_798467 409997357753632727890423 := by
  unfold tailWord_798467
  simp only [CollatzResearch.WordTrace]
  refine ⟨29122483998297901151953655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19414989332198600767969103 29122483998297901151953655)
  ·
    refine ⟨43683725997446851727930483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29122483998297901151953655 43683725997446851727930483)
    ·
      refine ⟨65525588996170277591895725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43683725997446851727930483 65525588996170277591895725)
      ·
        refine ⟨24572095873563854096960897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65525588996170277591895725 24572095873563854096960897)
        ·
          refine ⟨18429071905172890572720673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24572095873563854096960897 18429071905172890572720673)
          ·
            refine ⟨13821803928879667929540505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18429071905172890572720673 13821803928879667929540505)
            ·
              refine ⟨10366352946659750947155379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13821803928879667929540505 10366352946659750947155379)
              ·
                refine ⟨15549529419989626420733069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10366352946659750947155379 15549529419989626420733069)
                ·
                  refine ⟨5831073532496109907774901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15549529419989626420733069 5831073532496109907774901)
                  ·
                    refine ⟨546663143671510303853897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5831073532496109907774901 546663143671510303853897)
                    ·
                      refine ⟨409997357753632727890423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 546663143671510303853897 409997357753632727890423)
                      ·
                        rfl

theorem cell23_798467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 5, 2].length) (baseStart_798467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_798467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_798467 prefixEnd_798467 := by exact prefixLift 798467
  have htrace : WordTrace (prefixWord ++ tailWord_798467) baseStart_798467 baseEnd_798467 := by
    simpa [prefixWord, tailWord_798467, baseEnd_798467] using wordTrace_append hprefix tailTrace_798467
  have hstable : (prefixWord ++ tailWord_798467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798467).length < 2 ^ (prefixWord ++ tailWord_798467).sum := by decide
  have hdescent : baseEnd_798467 < baseStart_798467 := by decide
  rcases family_descends (prefixWord ++ tailWord_798467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798508 : List Nat := [2, 2, 1, 1, 1, 5, 4, 2, 1, 1, 3]
def baseStart_798508 : Nat := 118140960795 + 798508 * 2 ^ 59
def prefixEnd_798508 : Nat := 4983230072969 + 3 ^ 40 * 798508 * 2
def baseEnd_798508 : Nat := 410018410460467067477735

theorem tailTrace_798508 : CollatzResearch.WordTrace tailWord_798508 prefixEnd_798508 410018410460467067477735 := by
  unfold tailWord_798508
  simp only [CollatzResearch.WordTrace]
  refine ⟨14561989695574682577098089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19415986260766243436130785 14561989695574682577098089)
  ·
    refine ⟨10921492271681011932823567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14561989695574682577098089 10921492271681011932823567)
    ·
      refine ⟨16382238407521517899235351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10921492271681011932823567 16382238407521517899235351)
      ·
        refine ⟨24573357611282276848853027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16382238407521517899235351 24573357611282276848853027)
        ·
          refine ⟨36860036416923415273279541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24573357611282276848853027 36860036416923415273279541)
          ·
            refine ⟨3455628414086570181869957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36860036416923415273279541 3455628414086570181869957)
            ·
              refine ⟨647930327641231909100617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3455628414086570181869957 647930327641231909100617)
              ·
                refine ⟨485947745730923931825463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 647930327641231909100617 485947745730923931825463)
                ·
                  refine ⟨728921618596385897738195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 485947745730923931825463 728921618596385897738195)
                  ·
                    refine ⟨1093382427894578846607293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 728921618596385897738195 1093382427894578846607293)
                    ·
                      refine ⟨410018410460467067477735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1093382427894578846607293 410018410460467067477735)
                      ·
                        rfl

theorem cell23_798508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 4, 2, 1, 1, 3].length) (baseStart_798508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_798508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_798508 prefixEnd_798508 := by exact prefixLift 798508
  have htrace : WordTrace (prefixWord ++ tailWord_798508) baseStart_798508 baseEnd_798508 := by
    simpa [prefixWord, tailWord_798508, baseEnd_798508] using wordTrace_append hprefix tailTrace_798508
  have hstable : (prefixWord ++ tailWord_798508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798508).length < 2 ^ (prefixWord ++ tailWord_798508).sum := by decide
  have hdescent : baseEnd_798508 < baseStart_798508 := by decide
  rcases family_descends (prefixWord ++ tailWord_798508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798524 : List Nat := [2, 2, 2, 2, 1, 1, 4, 3, 2, 4]
def baseStart_798524 : Nat := 118140960795 + 798524 * 2 ^ 59
def prefixEnd_798524 : Nat := 4983230072969 + 3 ^ 40 * 798524 * 2
def baseEnd_798524 : Nat := 136675542050313001625887

theorem tailTrace_798524 : CollatzResearch.WordTrace tailWord_798524 prefixEnd_798524 136675542050313001625887 := by
  unfold tailWord_798524
  simp only [CollatzResearch.WordTrace]
  refine ⟨14562281479545699943389313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19416375306060933257852417 14562281479545699943389313)
  ·
    refine ⟨10921711109659274957541985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14562281479545699943389313 10921711109659274957541985)
    ·
      refine ⟨8191283332244456218156489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10921711109659274957541985 8191283332244456218156489)
      ·
        refine ⟨6143462499183342163617367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8191283332244456218156489 6143462499183342163617367)
        ·
          refine ⟨9215193748775013245426051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6143462499183342163617367 9215193748775013245426051)
          ·
            refine ⟨13822790623162519868139077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9215193748775013245426051 13822790623162519868139077)
            ·
              refine ⟨2591773241842972475276077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13822790623162519868139077 2591773241842972475276077)
              ·
                refine ⟨971914965691114678228529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2591773241842972475276077 971914965691114678228529)
                ·
                  refine ⟨728936224268336008671397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 971914965691114678228529 728936224268336008671397)
                  ·
                    refine ⟨136675542050313001625887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 728936224268336008671397 136675542050313001625887)
                    ·
                      rfl

theorem cell23_798524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 3, 2, 4].length) (baseStart_798524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_798524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_798524 prefixEnd_798524 := by exact prefixLift 798524
  have htrace : WordTrace (prefixWord ++ tailWord_798524) baseStart_798524 baseEnd_798524 := by
    simpa [prefixWord, tailWord_798524, baseEnd_798524] using wordTrace_append hprefix tailTrace_798524
  have hstable : (prefixWord ++ tailWord_798524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798524).length < 2 ^ (prefixWord ++ tailWord_798524).sum := by decide
  have hdescent : baseEnd_798524 < baseStart_798524 := by decide
  rcases family_descends (prefixWord ++ tailWord_798524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798531 : List Nat := [1, 1, 1, 3, 1, 6, 1, 2, 3, 2, 2]
def baseStart_798531 : Nat := 118140960795 + 798531 * 2 ^ 59
def prefixEnd_798531 : Nat := 4983230072969 + 3 ^ 40 * 798531 * 2
def baseEnd_798531 : Nat := 410030220515520477490129

theorem tailTrace_798531 : CollatzResearch.WordTrace tailWord_798531 prefixEnd_798531 410030220515520477490129 := by
  unfold tailWord_798531
  simp only [CollatzResearch.WordTrace]
  refine ⟨29124818270066040082283447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19416545513377360054855631 29124818270066040082283447)
  ·
    refine ⟨43687227405099060123425171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29124818270066040082283447 43687227405099060123425171)
    ·
      refine ⟨65530841107648590185137757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43687227405099060123425171 65530841107648590185137757)
      ·
        refine ⟨24574065415368221319426659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65530841107648590185137757 24574065415368221319426659)
        ·
          refine ⟨36861098123052331979139989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24574065415368221319426659 36861098123052331979139989)
          ·
            refine ⟨1727863974518078061522187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 36861098123052331979139989 1727863974518078061522187)
            ·
              refine ⟨2591795961777117092283281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1727863974518078061522187 2591795961777117092283281)
              ·
                refine ⟨1943846971332837819212461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2591795961777117092283281 1943846971332837819212461)
                ·
                  refine ⟨728942614249814182204673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1943846971332837819212461 728942614249814182204673)
                  ·
                    refine ⟨546706960687360636653505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 728942614249814182204673 546706960687360636653505)
                    ·
                      refine ⟨410030220515520477490129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 546706960687360636653505 410030220515520477490129)
                      ·
                        rfl

theorem cell23_798531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 2, 3, 2, 2].length) (baseStart_798531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_798531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_798531 prefixEnd_798531 := by exact prefixLift 798531
  have htrace : WordTrace (prefixWord ++ tailWord_798531) baseStart_798531 baseEnd_798531 := by
    simpa [prefixWord, tailWord_798531, baseEnd_798531] using wordTrace_append hprefix tailTrace_798531
  have hstable : (prefixWord ++ tailWord_798531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798531).length < 2 ^ (prefixWord ++ tailWord_798531).sum := by decide
  have hdescent : baseEnd_798531 < baseStart_798531 := by decide
  rcases family_descends (prefixWord ++ tailWord_798531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798537 : List Nat := [1, 2, 1, 1, 2, 4, 5, 7]
def baseStart_798537 : Nat := 118140960795 + 798537 * 2 ^ 59
def prefixEnd_798537 : Nat := 4983230072969 + 3 ^ 40 * 798537 * 2
def baseEnd_798537 : Nat := 15186418570349905704263

theorem tailTrace_798537 : CollatzResearch.WordTrace tailWord_798537 prefixEnd_798537 15186418570349905704263 := by
  unfold tailWord_798537
  simp only [CollatzResearch.WordTrace]
  refine ⟨29125037108044303107001865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19416691405362868738001243 29125037108044303107001865)
  ·
    refine ⟨21843777831033227330251399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29125037108044303107001865 21843777831033227330251399)
    ·
      refine ⟨32765666746549840995377099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21843777831033227330251399 32765666746549840995377099)
      ·
        refine ⟨49148500119824761493065649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32765666746549840995377099 49148500119824761493065649)
        ·
          refine ⟨36861375089868571119799237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49148500119824761493065649 36861375089868571119799237)
          ·
            refine ⟨6911507829350357084962357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36861375089868571119799237 6911507829350357084962357)
            ·
              refine ⟨647953859001595976715221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6911507829350357084962357 647953859001595976715221)
              ·
                refine ⟨15186418570349905704263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 647953859001595976715221 15186418570349905704263)
                ·
                  rfl

theorem cell23_798537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5, 7].length) (baseStart_798537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_798537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_798537 prefixEnd_798537 := by exact prefixLift 798537
  have htrace : WordTrace (prefixWord ++ tailWord_798537) baseStart_798537 baseEnd_798537 := by
    simpa [prefixWord, tailWord_798537, baseEnd_798537] using wordTrace_append hprefix tailTrace_798537
  have hstable : (prefixWord ++ tailWord_798537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798537).length < 2 ^ (prefixWord ++ tailWord_798537).sum := by decide
  have hdescent : baseEnd_798537 < baseStart_798537 := by decide
  rcases family_descends (prefixWord ++ tailWord_798537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798548 : List Nat := [2, 4, 1, 1, 3, 3, 2, 1, 1, 1, 4]
def baseStart_798548 : Nat := 118140960795 + 798548 * 2 ^ 59
def prefixEnd_798548 : Nat := 4983230072969 + 3 ^ 40 * 798548 * 2
def baseEnd_798548 : Nat := 410038949686646910977551

theorem tailTrace_798548 : CollatzResearch.WordTrace tailWord_798548 prefixEnd_798548 410038949686646910977551 := by
  unfold tailWord_798548
  simp only [CollatzResearch.WordTrace]
  refine ⟨14562719155502225992826149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19416958874002967990434865 14562719155502225992826149)
  ·
    refine ⟨2730509841656667373654903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14562719155502225992826149 2730509841656667373654903)
    ·
      refine ⟨4095764762485001060482355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2730509841656667373654903 4095764762485001060482355)
      ·
        refine ⟨6143647143727501590723533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4095764762485001060482355 6143647143727501590723533)
        ·
          refine ⟨2303867678897813096521325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6143647143727501590723533 2303867678897813096521325)
          ·
            refine ⟨863950379586679911195497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2303867678897813096521325 863950379586679911195497)
            ·
              refine ⟨647962784690009933396623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 863950379586679911195497 647962784690009933396623)
              ·
                refine ⟨971944177035014900094935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 647962784690009933396623 971944177035014900094935)
                ·
                  refine ⟨1457916265552522350142403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 971944177035014900094935 1457916265552522350142403)
                  ·
                    refine ⟨2186874398328783525213605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1457916265552522350142403 2186874398328783525213605)
                    ·
                      refine ⟨410038949686646910977551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2186874398328783525213605 410038949686646910977551)
                      ·
                        rfl

theorem cell23_798548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 2, 1, 1, 1, 4].length) (baseStart_798548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_798548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_798548 prefixEnd_798548 := by exact prefixLift 798548
  have htrace : WordTrace (prefixWord ++ tailWord_798548) baseStart_798548 baseEnd_798548 := by
    simpa [prefixWord, tailWord_798548, baseEnd_798548] using wordTrace_append hprefix tailTrace_798548
  have hstable : (prefixWord ++ tailWord_798548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798548).length < 2 ^ (prefixWord ++ tailWord_798548).sum := by decide
  have hdescent : baseEnd_798548 < baseStart_798548 := by decide
  rcases family_descends (prefixWord ++ tailWord_798548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798551 : List Nat := [1, 1, 3, 2, 5, 1, 1, 3, 1, 2, 3]
def baseStart_798551 : Nat := 118140960795 + 798551 * 2 ^ 59
def prefixEnd_798551 : Nat := 4983230072969 + 3 ^ 40 * 798551 * 2
def baseEnd_798551 : Nat := 410040490128610399240037

theorem tailTrace_798551 : CollatzResearch.WordTrace tailWord_798551 prefixEnd_798551 410040490128610399240037 := by
  unfold tailWord_798551
  simp only [CollatzResearch.WordTrace]
  refine ⟨29125547729993583498011507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19417031819995722332007671 29125547729993583498011507)
  ·
    refine ⟨43688321594990375247017261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29125547729993583498011507 43688321594990375247017261)
    ·
      refine ⟨16383120598121390717631473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43688321594990375247017261 16383120598121390717631473)
      ·
        refine ⟨12287340448591043038223605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16383120598121390717631473 12287340448591043038223605)
        ·
          refine ⟨1151938167055410284833463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12287340448591043038223605 1151938167055410284833463)
          ·
            refine ⟨1727907250583115427250195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1151938167055410284833463 1727907250583115427250195)
            ·
              refine ⟨2591860875874673140875293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1727907250583115427250195 2591860875874673140875293)
              ·
                refine ⟨971947828453002427828235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2591860875874673140875293 971947828453002427828235)
                ·
                  refine ⟨1457921742679503641742353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 971947828453002427828235 1457921742679503641742353)
                  ·
                    refine ⟨1093441307009627731306765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1457921742679503641742353 1093441307009627731306765)
                    ·
                      refine ⟨410040490128610399240037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1093441307009627731306765 410040490128610399240037)
                      ·
                        rfl

theorem cell23_798551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 3, 1, 2, 3].length) (baseStart_798551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_798551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_798551 prefixEnd_798551 := by exact prefixLift 798551
  have htrace : WordTrace (prefixWord ++ tailWord_798551) baseStart_798551 baseEnd_798551 := by
    simpa [prefixWord, tailWord_798551, baseEnd_798551] using wordTrace_append hprefix tailTrace_798551
  have hstable : (prefixWord ++ tailWord_798551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798551).length < 2 ^ (prefixWord ++ tailWord_798551).sum := by decide
  have hdescent : baseEnd_798551 < baseStart_798551 := by decide
  rcases family_descends (prefixWord ++ tailWord_798551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798604 : List Nat := [2, 2, 1, 2, 1, 2, 1, 3, 3, 4, 2]
def baseStart_798604 : Nat := 118140960795 + 798604 * 2 ^ 59
def prefixEnd_798604 : Nat := 4983230072969 + 3 ^ 40 * 798604 * 2
def baseEnd_798604 : Nat := 410067704603298691877293

theorem tailTrace_798604 : CollatzResearch.WordTrace tailWord_798604 prefixEnd_798604 410067704603298691877293 := by
  unfold tailWord_798604
  simp only [CollatzResearch.WordTrace]
  refine ⟨14563740399400786774845433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19418320532534382366460577 14563740399400786774845433)
  ·
    refine ⟨10922805299550590081134075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14563740399400786774845433 10922805299550590081134075)
    ·
      refine ⟨16384207949325885121701113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10922805299550590081134075 16384207949325885121701113)
      ·
        refine ⟨12288155961994413841275835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16384207949325885121701113 12288155961994413841275835)
        ·
          refine ⟨18432233942991620761913753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12288155961994413841275835 18432233942991620761913753)
          ·
            refine ⟨13824175457243715571435315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18432233942991620761913753 13824175457243715571435315)
            ·
              refine ⟨20736263185865573357152973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13824175457243715571435315 20736263185865573357152973)
              ·
                refine ⟨7776098694699590008932365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20736263185865573357152973 7776098694699590008932365)
                ·
                  refine ⟨2916037010512346253349637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7776098694699590008932365 2916037010512346253349637)
                  ·
                    refine ⟨546756939471064922503057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2916037010512346253349637 546756939471064922503057)
                    ·
                      refine ⟨410067704603298691877293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 546756939471064922503057 410067704603298691877293)
                      ·
                        rfl

theorem cell23_798604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 3, 4, 2].length) (baseStart_798604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_798604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_798604 prefixEnd_798604 := by exact prefixLift 798604
  have htrace : WordTrace (prefixWord ++ tailWord_798604) baseStart_798604 baseEnd_798604 := by
    simpa [prefixWord, tailWord_798604, baseEnd_798604] using wordTrace_append hprefix tailTrace_798604
  have hstable : (prefixWord ++ tailWord_798604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798604).length < 2 ^ (prefixWord ++ tailWord_798604).sum := by decide
  have hdescent : baseEnd_798604 < baseStart_798604 := by decide
  rcases family_descends (prefixWord ++ tailWord_798604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798617 : List Nat := [1, 2, 1, 2, 1, 3, 2, 1, 4, 2, 4]
def baseStart_798617 : Nat := 118140960795 + 798617 * 2 ^ 59
def prefixEnd_798617 : Nat := 4983230072969 + 3 ^ 40 * 798617 * 2
def baseEnd_798617 : Nat := 410074379851807141014733

theorem tailTrace_798617 : CollatzResearch.WordTrace tailWord_798617 prefixEnd_798617 410074379851807141014733 := by
  unfold tailWord_798617
  simp only [CollatzResearch.WordTrace]
  refine ⟨29127954947754476769914105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19418636631836317846609403 29127954947754476769914105)
  ·
    refine ⟨21845966210815857577435579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29127954947754476769914105 21845966210815857577435579)
    ·
      refine ⟨32768949316223786366153369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21845966210815857577435579 32768949316223786366153369)
      ·
        refine ⟨24576711987167839774615027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32768949316223786366153369 24576711987167839774615027)
        ·
          refine ⟨36865067980751759661922541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24576711987167839774615027 36865067980751759661922541)
          ·
            refine ⟨13824400492781909873220953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36865067980751759661922541 13824400492781909873220953)
            ·
              refine ⟨10368300369586432404915715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13824400492781909873220953 10368300369586432404915715)
              ·
                refine ⟨15552450554379648607373573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10368300369586432404915715 15552450554379648607373573)
                ·
                  refine ⟨2916084478946184113882545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15552450554379648607373573 2916084478946184113882545)
                  ·
                    refine ⟨2187063359209638085411909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2916084478946184113882545 2187063359209638085411909)
                    ·
                      refine ⟨410074379851807141014733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2187063359209638085411909 410074379851807141014733)
                      ·
                        rfl

theorem cell23_798617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 4, 2, 4].length) (baseStart_798617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_798617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_798617 prefixEnd_798617 := by exact prefixLift 798617
  have htrace : WordTrace (prefixWord ++ tailWord_798617) baseStart_798617 baseEnd_798617 := by
    simpa [prefixWord, tailWord_798617, baseEnd_798617] using wordTrace_append hprefix tailTrace_798617
  have hstable : (prefixWord ++ tailWord_798617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798617).length < 2 ^ (prefixWord ++ tailWord_798617).sum := by decide
  have hdescent : baseEnd_798617 < baseStart_798617 := by decide
  rcases family_descends (prefixWord ++ tailWord_798617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798667 : List Nat := [1, 1, 1, 1, 3, 4, 1, 1, 3, 2, 5]
def baseStart_798667 : Nat := 118140960795 + 798667 * 2 ^ 59
def prefixEnd_798667 : Nat := 4983230072969 + 3 ^ 40 * 798667 * 2
def baseEnd_798667 : Nat := 410100053884531945389503

theorem tailTrace_798667 : CollatzResearch.WordTrace tailWord_798667 prefixEnd_798667 410100053884531945389503 := by
  unfold tailWord_798667
  simp only [CollatzResearch.WordTrace]
  refine ⟨29129778597573335309234255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19419852398382223539489503 29129778597573335309234255)
  ·
    refine ⟨43694667896360002963851383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29129778597573335309234255 43694667896360002963851383)
    ·
      refine ⟨65542001844540004445777075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43694667896360002963851383 65542001844540004445777075)
      ·
        refine ⟨98313002766810006668665613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65542001844540004445777075 98313002766810006668665613)
        ·
          refine ⟨36867376037553752500749605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98313002766810006668665613 36867376037553752500749605)
          ·
            refine ⟨6912633007041328593890551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36867376037553752500749605 6912633007041328593890551)
            ·
              refine ⟨10368949510561992890835827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6912633007041328593890551 10368949510561992890835827)
              ·
                refine ⟨15553424265842989336253741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10368949510561992890835827 15553424265842989336253741)
                ·
                  refine ⟨5832534099691121001095153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15553424265842989336253741 5832534099691121001095153)
                  ·
                    refine ⟨4374400574768340750821365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5832534099691121001095153 4374400574768340750821365)
                    ·
                      refine ⟨410100053884531945389503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4374400574768340750821365 410100053884531945389503)
                      ·
                        rfl

theorem cell23_798667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 2, 5].length) (baseStart_798667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_798667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_798667 prefixEnd_798667 := by exact prefixLift 798667
  have htrace : WordTrace (prefixWord ++ tailWord_798667) baseStart_798667 baseEnd_798667 := by
    simpa [prefixWord, tailWord_798667, baseEnd_798667] using wordTrace_append hprefix tailTrace_798667
  have hstable : (prefixWord ++ tailWord_798667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798667).length < 2 ^ (prefixWord ++ tailWord_798667).sum := by decide
  have hdescent : baseEnd_798667 < baseStart_798667 := by decide
  rcases family_descends (prefixWord ++ tailWord_798667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798704 : List Nat := [2, 1, 1, 1, 3, 2, 3, 1, 5, 4]
def baseStart_798704 : Nat := 118140960795 + 798704 * 2 ^ 59
def prefixEnd_798704 : Nat := 4983230072969 + 3 ^ 40 * 798704 * 2
def baseEnd_798704 : Nat := 136706350889582766875611

theorem tailTrace_798704 : CollatzResearch.WordTrace tailWord_798704 prefixEnd_798704 136706350889582766875611 := by
  unfold tailWord_798704
  simp only [CollatzResearch.WordTrace]
  refine ⟨14565564049219645314165583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19420752065626193752220777 14565564049219645314165583)
  ·
    refine ⟨21848346073829467971248375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14565564049219645314165583 21848346073829467971248375)
    ·
      refine ⟨32772519110744201956872563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21848346073829467971248375 32772519110744201956872563)
      ·
        refine ⟨49158778666116302935308845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32772519110744201956872563 49158778666116302935308845)
        ·
          refine ⟨18434541999793613600740817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49158778666116302935308845 18434541999793613600740817)
          ·
            refine ⟨13825906499845210200555613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18434541999793613600740817 13825906499845210200555613)
            ·
              refine ⟨5184714937441953825208355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13825906499845210200555613 5184714937441953825208355)
              ·
                refine ⟨7777072406162930737812533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5184714937441953825208355 7777072406162930737812533)
                ·
                  refine ⟨729100538077774756669925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7777072406162930737812533 729100538077774756669925)
                  ·
                    refine ⟨136706350889582766875611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 729100538077774756669925 136706350889582766875611)
                    ·
                      rfl

theorem cell23_798704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 5, 4].length) (baseStart_798704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_798704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_798704 prefixEnd_798704 := by exact prefixLift 798704
  have htrace : WordTrace (prefixWord ++ tailWord_798704) baseStart_798704 baseEnd_798704 := by
    simpa [prefixWord, tailWord_798704, baseEnd_798704] using wordTrace_append hprefix tailTrace_798704
  have hstable : (prefixWord ++ tailWord_798704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798704).length < 2 ^ (prefixWord ++ tailWord_798704).sum := by decide
  have hdescent : baseEnd_798704 < baseStart_798704 := by decide
  rcases family_descends (prefixWord ++ tailWord_798704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798707 : List Nat := [1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 6]
def baseStart_798707 : Nat := 118140960795 + 798707 * 2 ^ 59
def prefixEnd_798707 : Nat := 4983230072969 + 3 ^ 40 * 798707 * 2
def baseEnd_798707 : Nat := 410120593110711788889319

theorem tailTrace_798707 : CollatzResearch.WordTrace tailWord_798707 prefixEnd_798707 410120593110711788889319 := by
  unfold tailWord_798707
  simp only [CollatzResearch.WordTrace]
  refine ⟨29131237517428422140690375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19420825011618948093793583 29131237517428422140690375)
  ·
    refine ⟨43696856276142633211035563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29131237517428422140690375 43696856276142633211035563)
    ·
      refine ⟨65545284414213949816553345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43696856276142633211035563 65545284414213949816553345)
      ·
        refine ⟨49158963310660462362415009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65545284414213949816553345 49158963310660462362415009)
        ·
          refine ⟨36869222482995346771811257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49158963310660462362415009 36869222482995346771811257)
          ·
            refine ⟨27651916862246510078858443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36869222482995346771811257 27651916862246510078858443)
            ·
              refine ⟨41477875293369765118287665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27651916862246510078858443 41477875293369765118287665)
              ·
                refine ⟨31108406470027323838715749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41477875293369765118287665 31108406470027323838715749)
                ·
                  refine ⟨5832826213130123219759203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31108406470027323838715749 5832826213130123219759203)
                  ·
                    refine ⟨8749239319695184829638805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5832826213130123219759203 8749239319695184829638805)
                    ·
                      refine ⟨410120593110711788889319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8749239319695184829638805 410120593110711788889319)
                      ·
                        rfl

theorem cell23_798707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 6].length) (baseStart_798707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_798707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_798707 prefixEnd_798707 := by exact prefixLift 798707
  have htrace : WordTrace (prefixWord ++ tailWord_798707) baseStart_798707 baseEnd_798707 := by
    simpa [prefixWord, tailWord_798707, baseEnd_798707] using wordTrace_append hprefix tailTrace_798707
  have hstable : (prefixWord ++ tailWord_798707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798707).length < 2 ^ (prefixWord ++ tailWord_798707).sum := by decide
  have hdescent : baseEnd_798707 < baseStart_798707 := by decide
  rcases family_descends (prefixWord ++ tailWord_798707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798734 : List Nat := [4, 1, 1, 2, 2, 1, 3, 1, 8]
def baseStart_798734 : Nat := 118140960795 + 798734 * 2 ^ 59
def prefixEnd_798734 : Nat := 4983230072969 + 3 ^ 40 * 798734 * 2
def baseEnd_798734 : Nat := 45570495232042575916855

theorem tailTrace_798734 : CollatzResearch.WordTrace tailWord_798734 prefixEnd_798734 45570495232042575916855 := by
  unfold tailWord_798734
  simp only [CollatzResearch.WordTrace]
  refine ⟨3641527786041325718990407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19421481525553737167948837 3641527786041325718990407)
  ·
    refine ⟨5462291679061988578485611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3641527786041325718990407 5462291679061988578485611)
    ·
      refine ⟨8193437518592982867728417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5462291679061988578485611 8193437518592982867728417)
      ·
        refine ⟨6145078138944737150796313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8193437518592982867728417 6145078138944737150796313)
        ·
          refine ⟨4608808604208552863097235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6145078138944737150796313 4608808604208552863097235)
          ·
            refine ⟨6913212906312829294645853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4608808604208552863097235 6913212906312829294645853)
            ·
              refine ⟨2592454839867310985492195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6913212906312829294645853 2592454839867310985492195)
              ·
                refine ⟨3888682259800966478238293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2592454839867310985492195 3888682259800966478238293)
                ·
                  refine ⟨45570495232042575916855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3888682259800966478238293 45570495232042575916855)
                  ·
                    rfl

theorem cell23_798734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 8].length) (baseStart_798734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_798734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_798734 prefixEnd_798734 := by exact prefixLift 798734
  have htrace : WordTrace (prefixWord ++ tailWord_798734) baseStart_798734 baseEnd_798734 := by
    simpa [prefixWord, tailWord_798734, baseEnd_798734] using wordTrace_append hprefix tailTrace_798734
  have hstable : (prefixWord ++ tailWord_798734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798734).length < 2 ^ (prefixWord ++ tailWord_798734).sum := by decide
  have hdescent : baseEnd_798734 < baseStart_798734 := by decide
  rcases family_descends (prefixWord ++ tailWord_798734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798747 : List Nat := [1, 1, 1, 1, 1, 1, 3, 3, 2, 9]
def baseStart_798747 : Nat := 118140960795 + 798747 * 2 ^ 59
def prefixEnd_798747 : Nat := 4983230072969 + 3 ^ 40 * 798747 * 2
def baseEnd_798747 : Nat := 136713710778963877463045

theorem tailTrace_798747 : CollatzResearch.WordTrace tailWord_798747 prefixEnd_798747 136713710778963877463045 := by
  unfold tailWord_798747
  simp only [CollatzResearch.WordTrace]
  refine ⟨29132696437283508972146495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19421797624855672648097663 29132696437283508972146495)
  ·
    refine ⟨43699044655925263458219743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29132696437283508972146495 43699044655925263458219743)
    ·
      refine ⟨65548566983887895187329615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43699044655925263458219743 65548566983887895187329615)
      ·
        refine ⟨98322850475831842780994423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65548566983887895187329615 98322850475831842780994423)
        ·
          refine ⟨147484275713747764171491635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98322850475831842780994423 147484275713747764171491635)
          ·
            refine ⟨221226413570621646257237453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147484275713747764171491635 221226413570621646257237453)
            ·
              refine ⟨82959905088983117346464045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 221226413570621646257237453 82959905088983117346464045)
              ·
                refine ⟨31109964408368669004924017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82959905088983117346464045 31109964408368669004924017)
                ·
                  refine ⟨23332473306276501753693013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31109964408368669004924017 23332473306276501753693013)
                  ·
                    refine ⟨136713710778963877463045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 23332473306276501753693013 136713710778963877463045)
                    ·
                      rfl

theorem cell23_798747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 9].length) (baseStart_798747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_798747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_798747 prefixEnd_798747 := by exact prefixLift 798747
  have htrace : WordTrace (prefixWord ++ tailWord_798747) baseStart_798747 baseEnd_798747 := by
    simpa [prefixWord, tailWord_798747, baseEnd_798747] using wordTrace_append hprefix tailTrace_798747
  have hstable : (prefixWord ++ tailWord_798747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798747).length < 2 ^ (prefixWord ++ tailWord_798747).sum := by decide
  have hdescent : baseEnd_798747 < baseStart_798747 := by decide
  rcases family_descends (prefixWord ++ tailWord_798747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798751 : List Nat := [1, 1, 2, 4, 1, 2, 5, 1, 6]
def baseStart_798751 : Nat := 118140960795 + 798751 * 2 ^ 59
def prefixEnd_798751 : Nat := 4983230072969 + 3 ^ 40 * 798751 * 2
def baseEnd_798751 : Nat := 45571465139945512971013

theorem tailTrace_798751 : CollatzResearch.WordTrace tailWord_798751 prefixEnd_798751 45571465139945512971013 := by
  unfold tailWord_798751
  simp only [CollatzResearch.WordTrace]
  refine ⟨29132842329269017655292107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19421894886179345103528071 29132842329269017655292107)
  ·
    refine ⟨43699263493903526482938161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29132842329269017655292107 43699263493903526482938161)
    ·
      refine ⟨32774447620427644862203621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43699263493903526482938161 32774447620427644862203621)
      ·
        refine ⟨6145208928830183411663179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32774447620427644862203621 6145208928830183411663179)
        ·
          refine ⟨9217813393245275117494769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6145208928830183411663179 9217813393245275117494769)
          ·
            refine ⟨6913360044933956338121077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9217813393245275117494769 6913360044933956338121077)
            ·
              refine ⟨648127504212558406698851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6913360044933956338121077 648127504212558406698851)
              ·
                refine ⟨972191256318837610048277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 648127504212558406698851 972191256318837610048277)
                ·
                  refine ⟨45571465139945512971013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 972191256318837610048277 45571465139945512971013)
                  ·
                    rfl

theorem cell23_798751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5, 1, 6].length) (baseStart_798751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_798751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_798751 prefixEnd_798751 := by exact prefixLift 798751
  have htrace : WordTrace (prefixWord ++ tailWord_798751) baseStart_798751 baseEnd_798751 := by
    simpa [prefixWord, tailWord_798751, baseEnd_798751] using wordTrace_append hprefix tailTrace_798751
  have hstable : (prefixWord ++ tailWord_798751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798751).length < 2 ^ (prefixWord ++ tailWord_798751).sum := by decide
  have hdescent : baseEnd_798751 < baseStart_798751 := by decide
  rcases family_descends (prefixWord ++ tailWord_798751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798754 : List Nat := [3, 3, 1, 1, 1, 2, 1, 2, 1, 2, 6]
def baseStart_798754 : Nat := 118140960795 + 798754 * 2 ^ 59
def prefixEnd_798754 : Nat := 4983230072969 + 3 ^ 40 * 798754 * 2
def baseEnd_798754 : Nat := 410144726701473105001603

theorem tailTrace_798754 : CollatzResearch.WordTrace tailWord_798754 prefixEnd_798754 410144726701473105001603 := by
  unfold tailWord_798754
  simp only [CollatzResearch.WordTrace]
  refine ⟨7283237937064537291912829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19421967832172099445100877 7283237937064537291912829)
  ·
    refine ⟨2731214226399201484467311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7283237937064537291912829 2731214226399201484467311)
    ·
      refine ⟨4096821339598802226700967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2731214226399201484467311 4096821339598802226700967)
      ·
        refine ⟨6145232009398203340051451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4096821339598802226700967 6145232009398203340051451)
        ·
          refine ⟨9217848014097305010077177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6145232009398203340051451 9217848014097305010077177)
          ·
            refine ⟨6913386010572978757557883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9217848014097305010077177 6913386010572978757557883)
            ·
              refine ⟨10370079015859468136336825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6913386010572978757557883 10370079015859468136336825)
              ·
                refine ⟨7777559261894601102252619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10370079015859468136336825 7777559261894601102252619)
                ·
                  refine ⟨11666338892841901653378929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7777559261894601102252619 11666338892841901653378929)
                  ·
                    refine ⟨8749754169631426240034197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11666338892841901653378929 8749754169631426240034197)
                    ·
                      refine ⟨410144726701473105001603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8749754169631426240034197 410144726701473105001603)
                      ·
                        rfl

theorem cell23_798754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_798754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_798754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_798754 prefixEnd_798754 := by exact prefixLift 798754
  have htrace : WordTrace (prefixWord ++ tailWord_798754) baseStart_798754 baseEnd_798754 := by
    simpa [prefixWord, tailWord_798754, baseEnd_798754] using wordTrace_append hprefix tailTrace_798754
  have hstable : (prefixWord ++ tailWord_798754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798754).length < 2 ^ (prefixWord ++ tailWord_798754).sum := by decide
  have hdescent : baseEnd_798754 < baseStart_798754 := by decide
  rcases family_descends (prefixWord ++ tailWord_798754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798771 : List Nat := [1, 1, 1, 2, 4, 1, 4, 1, 1, 5, 2]
def baseStart_798771 : Nat := 118140960795 + 798771 * 2 ^ 59
def prefixEnd_798771 : Nat := 4983230072969 + 3 ^ 40 * 798771 * 2
def baseEnd_798771 : Nat := 410153455872599538489025

theorem tailTrace_798771 : CollatzResearch.WordTrace tailWord_798771 prefixEnd_798771 410153455872599538489025 := by
  unfold tailWord_798771
  simp only [CollatzResearch.WordTrace]
  refine ⟨29133571789196561071020167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19422381192797707380680111 29133571789196561071020167)
  ·
    refine ⟨43700357683794841606530251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29133571789196561071020167 43700357683794841606530251)
    ·
      refine ⟨65550536525692262409795377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43700357683794841606530251 65550536525692262409795377)
      ·
        refine ⟨49162902394269196807346533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65550536525692262409795377 49162902394269196807346533)
        ·
          refine ⟨9218044198925474401377475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49162902394269196807346533 9218044198925474401377475)
          ·
            refine ⟨13827066298388211602066213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9218044198925474401377475 13827066298388211602066213)
            ·
              refine ⟨2592574930947789675387415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13827066298388211602066213 2592574930947789675387415)
              ·
                refine ⟨3888862396421684513081123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2592574930947789675387415 3888862396421684513081123)
                ·
                  refine ⟨5833293594632526769621685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3888862396421684513081123 5833293594632526769621685)
                  ·
                    refine ⟨546871274496799384652033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5833293594632526769621685 546871274496799384652033)
                    ·
                      refine ⟨410153455872599538489025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 546871274496799384652033 410153455872599538489025)
                      ·
                        rfl

theorem cell23_798771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 5, 2].length) (baseStart_798771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_798771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_798771 prefixEnd_798771 := by exact prefixLift 798771
  have htrace : WordTrace (prefixWord ++ tailWord_798771) baseStart_798771 baseEnd_798771 := by
    simpa [prefixWord, tailWord_798771, baseEnd_798771] using wordTrace_append hprefix tailTrace_798771
  have hstable : (prefixWord ++ tailWord_798771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798771).length < 2 ^ (prefixWord ++ tailWord_798771).sum := by decide
  have hdescent : baseEnd_798771 < baseStart_798771 := by decide
  rcases family_descends (prefixWord ++ tailWord_798771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798781 : List Nat := [1, 4, 1, 3, 1, 1, 1, 5, 1, 5]
def baseStart_798781 : Nat := 118140960795 + 798781 * 2 ^ 59
def prefixEnd_798781 : Nat := 4983230072969 + 3 ^ 40 * 798781 * 2
def baseEnd_798781 : Nat := 136719530226381499787993

theorem tailTrace_798781 : CollatzResearch.WordTrace tailWord_798781 prefixEnd_798781 136719530226381499787993 := by
  unfold tailWord_798781
  simp only [CollatzResearch.WordTrace]
  refine ⟨29133936519160332778884197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19422624346106888519256131 29133936519160332778884197)
  ·
    refine ⟨5462613097342562396040787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29133936519160332778884197 5462613097342562396040787)
    ·
      refine ⟨8193919646013843594061181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5462613097342562396040787 8193919646013843594061181)
      ·
        refine ⟨3072719867255191347772943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8193919646013843594061181 3072719867255191347772943)
        ·
          refine ⟨4609079800882787021659415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3072719867255191347772943 4609079800882787021659415)
          ·
            refine ⟨6913619701324180532489123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4609079800882787021659415 6913619701324180532489123)
            ·
              refine ⟨10370429551986270798733685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6913619701324180532489123 10370429551986270798733685)
              ·
                refine ⟨972227770498712887381283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10370429551986270798733685 972227770498712887381283)
                ·
                  refine ⟨1458341655748069331071925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 972227770498712887381283 1458341655748069331071925)
                  ·
                    refine ⟨136719530226381499787993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1458341655748069331071925 136719530226381499787993)
                    ·
                      rfl

theorem cell23_798781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 5, 1, 5].length) (baseStart_798781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_798781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_798781 prefixEnd_798781 := by exact prefixLift 798781
  have htrace : WordTrace (prefixWord ++ tailWord_798781) baseStart_798781 baseEnd_798781 := by
    simpa [prefixWord, tailWord_798781, baseEnd_798781] using wordTrace_append hprefix tailTrace_798781
  have hstable : (prefixWord ++ tailWord_798781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798781).length < 2 ^ (prefixWord ++ tailWord_798781).sum := by decide
  have hdescent : baseEnd_798781 < baseStart_798781 := by decide
  rcases family_descends (prefixWord ++ tailWord_798781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798831 : List Nat := [1, 1, 2, 1, 3, 5, 1, 2, 1, 2, 4]
def baseStart_798831 : Nat := 118140960795 + 798831 * 2 ^ 59
def prefixEnd_798831 : Nat := 4983230072969 + 3 ^ 40 * 798831 * 2
def baseEnd_798831 : Nat := 410184264711869303738749

theorem tailTrace_798831 : CollatzResearch.WordTrace tailWord_798831 prefixEnd_798831 410184264711869303738749 := by
  unfold tailWord_798831
  simp only [CollatzResearch.WordTrace]
  refine ⟨29135760168979191318204347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19423840112652794212136231 29135760168979191318204347)
  ·
    refine ⟨43703640253468786977306521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29135760168979191318204347 43703640253468786977306521)
    ·
      refine ⟨32777730190101590232979891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43703640253468786977306521 32777730190101590232979891)
      ·
        refine ⟨49166595285152385349469837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32777730190101590232979891 49166595285152385349469837)
        ·
          refine ⟨18437473231932144506051189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49166595285152385349469837 18437473231932144506051189)
          ·
            refine ⟨1728513115493638547442299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18437473231932144506051189 1728513115493638547442299)
            ·
              refine ⟨2592769673240457821163449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1728513115493638547442299 2592769673240457821163449)
              ·
                refine ⟨1944577254930343365872587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2592769673240457821163449 1944577254930343365872587)
                ·
                  refine ⟨2916865882395515048808881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1944577254930343365872587 2916865882395515048808881)
                  ·
                    refine ⟨2187649411796636286606661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2916865882395515048808881 2187649411796636286606661)
                    ·
                      refine ⟨410184264711869303738749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2187649411796636286606661 410184264711869303738749)
                      ·
                        rfl

theorem cell23_798831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 2, 1, 2, 4].length) (baseStart_798831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_798831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_798831 prefixEnd_798831 := by exact prefixLift 798831
  have htrace : WordTrace (prefixWord ++ tailWord_798831) baseStart_798831 baseEnd_798831 := by
    simpa [prefixWord, tailWord_798831, baseEnd_798831] using wordTrace_append hprefix tailTrace_798831
  have hstable : (prefixWord ++ tailWord_798831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798831).length < 2 ^ (prefixWord ++ tailWord_798831).sum := by decide
  have hdescent : baseEnd_798831 < baseStart_798831 := by decide
  rcases family_descends (prefixWord ++ tailWord_798831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798838 : List Nat := [5, 1, 1, 2, 1, 2, 3, 1, 1, 1, 5]
def baseStart_798838 : Nat := 118140960795 + 798838 * 2 ^ 59
def prefixEnd_798838 : Nat := 4983230072969 + 3 ^ 40 * 798838 * 2
def baseEnd_798838 : Nat := 410187859076450776351217

theorem tailTrace_798838 : CollatzResearch.WordTrace tailWord_798838 prefixEnd_798838 410187859076450776351217 := by
  unfold tailWord_798838
  simp only [CollatzResearch.WordTrace]
  refine ⟨1821000967497114469606823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19424010319969221009139445 1821000967497114469606823)
  ·
    refine ⟨2731501451245671704410235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1821000967497114469606823 2731501451245671704410235)
    ·
      refine ⟨4097252176868507556615353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2731501451245671704410235 4097252176868507556615353)
      ·
        refine ⟨3072939132651380667461515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4097252176868507556615353 3072939132651380667461515)
        ·
          refine ⟨4609408698977071001192273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3072939132651380667461515 4609408698977071001192273)
          ·
            refine ⟨3457056524232803250894205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4609408698977071001192273 3457056524232803250894205)
            ·
              refine ⟨1296396196587301219085327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3457056524232803250894205 1296396196587301219085327)
              ·
                refine ⟨1944594294880951828627991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1296396196587301219085327 1944594294880951828627991)
                ·
                  refine ⟨2916891442321427742941987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1944594294880951828627991 2916891442321427742941987)
                  ·
                    refine ⟨4375337163482141614412981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2916891442321427742941987 4375337163482141614412981)
                    ·
                      refine ⟨410187859076450776351217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4375337163482141614412981 410187859076450776351217)
                      ·
                        rfl

theorem cell23_798838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_798838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_798838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_798838 prefixEnd_798838 := by exact prefixLift 798838
  have htrace : WordTrace (prefixWord ++ tailWord_798838) baseStart_798838 baseEnd_798838 := by
    simpa [prefixWord, tailWord_798838, baseEnd_798838] using wordTrace_append hprefix tailTrace_798838
  have hstable : (prefixWord ++ tailWord_798838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798838).length < 2 ^ (prefixWord ++ tailWord_798838).sum := by decide
  have hdescent : baseEnd_798838 < baseStart_798838 := by decide
  rcases family_descends (prefixWord ++ tailWord_798838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798852 : List Nat := [2, 3, 2, 1, 2, 1, 3, 4, 1, 2, 2]
def baseStart_798852 : Nat := 118140960795 + 798852 * 2 ^ 59
def prefixEnd_798852 : Nat := 4983230072969 + 3 ^ 40 * 798852 * 2
def baseEnd_798852 : Nat := 410195047805613721576153

theorem tailTrace_798852 : CollatzResearch.WordTrace tailWord_798852 prefixEnd_798852 410195047805613721576153 := by
  unfold tailWord_798852
  simp only [CollatzResearch.WordTrace]
  refine ⟨14568263050951555952359405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19424350734602074603145873 14568263050951555952359405)
  ·
    refine ⟨5463098644106833482134777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14568263050951555952359405 5463098644106833482134777)
    ·
      refine ⟨4097323983080125111601083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5463098644106833482134777 4097323983080125111601083)
      ·
        refine ⟨6145985974620187667401625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4097323983080125111601083 6145985974620187667401625)
        ·
          refine ⟨4609489480965140750551219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6145985974620187667401625 4609489480965140750551219)
          ·
            refine ⟨6914234221447711125826829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4609489480965140750551219 6914234221447711125826829)
            ·
              refine ⟨2592837833042891672185061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6914234221447711125826829 2592837833042891672185061)
              ·
                refine ⟨486157093695542188534699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2592837833042891672185061 486157093695542188534699)
                ·
                  refine ⟨729235640543313282802049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 486157093695542188534699 729235640543313282802049)
                  ·
                    refine ⟨546926730407484962101537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 729235640543313282802049 546926730407484962101537)
                    ·
                      refine ⟨410195047805613721576153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 546926730407484962101537 410195047805613721576153)
                      ·
                        rfl

theorem cell23_798852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 4, 1, 2, 2].length) (baseStart_798852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_798852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_798852 prefixEnd_798852 := by exact prefixLift 798852
  have htrace : WordTrace (prefixWord ++ tailWord_798852) baseStart_798852 baseEnd_798852 := by
    simpa [prefixWord, tailWord_798852, baseEnd_798852] using wordTrace_append hprefix tailTrace_798852
  have hstable : (prefixWord ++ tailWord_798852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798852).length < 2 ^ (prefixWord ++ tailWord_798852).sum := by decide
  have hdescent : baseEnd_798852 < baseStart_798852 := by decide
  rcases family_descends (prefixWord ++ tailWord_798852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798891 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 4, 8, 2]
def baseStart_798891 : Nat := 118140960795 + 798891 * 2 ^ 59
def prefixEnd_798891 : Nat := 4983230072969 + 3 ^ 40 * 798891 * 2
def baseEnd_798891 : Nat := 410215073551139068988473

theorem tailTrace_798891 : CollatzResearch.WordTrace tailWord_798891 prefixEnd_798891 410215073551139068988473 := by
  unfold tailWord_798891
  simp only [CollatzResearch.WordTrace]
  refine ⟨29137948548761821565388527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19425299032507881043592351 29137948548761821565388527)
  ·
    refine ⟨43706922823142732348082791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29137948548761821565388527 43706922823142732348082791)
    ·
      refine ⟨65560384234714098522124187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43706922823142732348082791 65560384234714098522124187)
      ·
        refine ⟨98340576352071147783186281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65560384234714098522124187 98340576352071147783186281)
        ·
          refine ⟨73755432264053360837389711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98340576352071147783186281 73755432264053360837389711)
          ·
            refine ⟨110633148396080041256084567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73755432264053360837389711 110633148396080041256084567)
            ·
              refine ⟨165949722594120061884126851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110633148396080041256084567 165949722594120061884126851)
              ·
                refine ⟨248924583891180092826190277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165949722594120061884126851 248924583891180092826190277)
                ·
                  refine ⟨46673359479596267404910677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 248924583891180092826190277 46673359479596267404910677)
                  ·
                    refine ⟨546953431401518758651297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 46673359479596267404910677 546953431401518758651297)
                    ·
                      refine ⟨410215073551139068988473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 546953431401518758651297 410215073551139068988473)
                      ·
                        rfl

theorem cell23_798891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 8, 2].length) (baseStart_798891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_798891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_798891 prefixEnd_798891 := by exact prefixLift 798891
  have htrace : WordTrace (prefixWord ++ tailWord_798891) baseStart_798891 baseEnd_798891 := by
    simpa [prefixWord, tailWord_798891, baseEnd_798891] using wordTrace_append hprefix tailTrace_798891
  have hstable : (prefixWord ++ tailWord_798891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798891).length < 2 ^ (prefixWord ++ tailWord_798891).sum := by decide
  have hdescent : baseEnd_798891 < baseStart_798891 := by decide
  rcases family_descends (prefixWord ++ tailWord_798891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798961 : List Nat := [1, 2, 2, 2, 2, 1, 3, 1, 4, 5]
def baseStart_798961 : Nat := 118140960795 + 798961 * 2 ^ 59
def prefixEnd_798961 : Nat := 4983230072969 + 3 ^ 40 * 798961 * 2
def baseEnd_798961 : Nat := 136750339065651265037717

theorem tailTrace_798961 : CollatzResearch.WordTrace tailWord_798961 prefixEnd_798961 136750339065651265037717 := by
  unfold tailWord_798961
  simp only [CollatzResearch.WordTrace]
  refine ⟨29140501658508223520436737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19427001105672149013624491 29140501658508223520436737)
  ·
    refine ⟨21855376243881167640327553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29140501658508223520436737 21855376243881167640327553)
    ·
      refine ⟨16391532182910875730245665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21855376243881167640327553 16391532182910875730245665)
      ·
        refine ⟨12293649137183156797684249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16391532182910875730245665 12293649137183156797684249)
        ·
          refine ⟨9220236852887367598263187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12293649137183156797684249 9220236852887367598263187)
          ·
            refine ⟨13830355279331051397394781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9220236852887367598263187 13830355279331051397394781)
            ·
              refine ⟨5186383229749144274023043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13830355279331051397394781 5186383229749144274023043)
              ·
                refine ⟨7779574844623716411034565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5186383229749144274023043 7779574844623716411034565)
                ·
                  refine ⟨1458670283366946827068981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7779574844623716411034565 1458670283366946827068981)
                  ·
                    refine ⟨136750339065651265037717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1458670283366946827068981 136750339065651265037717)
                    ·
                      rfl

theorem cell23_798961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 4, 5].length) (baseStart_798961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_798961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_798961 prefixEnd_798961 := by exact prefixLift 798961
  have htrace : WordTrace (prefixWord ++ tailWord_798961) baseStart_798961 baseEnd_798961 := by
    simpa [prefixWord, tailWord_798961, baseEnd_798961] using wordTrace_append hprefix tailTrace_798961
  have hstable : (prefixWord ++ tailWord_798961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798961).length < 2 ^ (prefixWord ++ tailWord_798961).sum := by decide
  have hdescent : baseEnd_798961 < baseStart_798961 := by decide
  rcases family_descends (prefixWord ++ tailWord_798961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798981 : List Nat := [1, 3, 1, 1, 2, 1, 2, 4, 1, 3, 4]
def baseStart_798981 : Nat := 118140960795 + 798981 * 2 ^ 59
def prefixEnd_798981 : Nat := 4983230072969 + 3 ^ 40 * 798981 * 2
def baseEnd_798981 : Nat := 410261286810043716863059

theorem tailTrace_798981 : CollatzResearch.WordTrace tailWord_798981 prefixEnd_798981 410261286810043716863059 := by
  unfold tailWord_798981
  simp only [CollatzResearch.WordTrace]
  refine ⟨29141231118435766936164797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19427487412290511290776531 29141231118435766936164797)
  ·
    refine ⟨10927961669413412601061799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29141231118435766936164797 10927961669413412601061799)
    ·
      refine ⟨16391942504120118901592699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10927961669413412601061799 16391942504120118901592699)
      ·
        refine ⟨24587913756180178352389049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16391942504120118901592699 24587913756180178352389049)
        ·
          refine ⟨18440935317135133764291787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24587913756180178352389049 18440935317135133764291787)
          ·
            refine ⟨27661402975702700646437681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18440935317135133764291787 27661402975702700646437681)
            ·
              refine ⟨20746052231777025484828261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27661402975702700646437681 20746052231777025484828261)
              ·
                refine ⟨3889884793458192278405299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20746052231777025484828261 3889884793458192278405299)
                ·
                  refine ⟨5834827190187288417607949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3889884793458192278405299 5834827190187288417607949)
                  ·
                    refine ⟨2188060196320233156602981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5834827190187288417607949 2188060196320233156602981)
                    ·
                      refine ⟨410261286810043716863059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2188060196320233156602981 410261286810043716863059)
                      ·
                        rfl

theorem cell23_798981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 3, 4].length) (baseStart_798981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_798981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_798981 prefixEnd_798981 := by exact prefixLift 798981
  have htrace : WordTrace (prefixWord ++ tailWord_798981) baseStart_798981 baseEnd_798981 := by
    simpa [prefixWord, tailWord_798981, baseEnd_798981] using wordTrace_append hprefix tailTrace_798981
  have hstable : (prefixWord ++ tailWord_798981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798981).length < 2 ^ (prefixWord ++ tailWord_798981).sum := by decide
  have hdescent : baseEnd_798981 < baseStart_798981 := by decide
  rcases family_descends (prefixWord ++ tailWord_798981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799011 : List Nat := [1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 6]
def baseStart_799011 : Nat := 118140960795 + 799011 * 2 ^ 59
def prefixEnd_799011 : Nat := 4983230072969 + 3 ^ 40 * 799011 * 2
def baseEnd_799011 : Nat := 410276691229678599487921

theorem tailTrace_799011 : CollatzResearch.WordTrace tailWord_799011 prefixEnd_799011 410276691229678599487921 := by
  unfold tailWord_799011
  simp only [CollatzResearch.WordTrace]
  refine ⟨29142325308327082059756887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19428216872218054706504591 29142325308327082059756887)
  ·
    refine ⟨43713487962490623089635331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29142325308327082059756887 43713487962490623089635331)
    ·
      refine ⟨65570231943735934634452997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43713487962490623089635331 65570231943735934634452997)
      ·
        refine ⟨12294418489450487743959937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65570231943735934634452997 12294418489450487743959937)
        ·
          refine ⟨9220813867087865807969953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12294418489450487743959937 9220813867087865807969953)
          ·
            refine ⟨6915610400315899355977465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9220813867087865807969953 6915610400315899355977465)
            ·
              refine ⟨5186707800236924516983099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6915610400315899355977465 5186707800236924516983099)
              ·
                refine ⟨7780061700355386775474649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5186707800236924516983099 7780061700355386775474649)
                ·
                  refine ⟨5835046275266540081605987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7780061700355386775474649 5835046275266540081605987)
                  ·
                    refine ⟨8752569412899810122408981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5835046275266540081605987 8752569412899810122408981)
                    ·
                      refine ⟨410276691229678599487921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8752569412899810122408981 410276691229678599487921)
                      ·
                        rfl

theorem cell23_799011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_799011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_799011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_799011 prefixEnd_799011 := by exact prefixLift 799011
  have htrace : WordTrace (prefixWord ++ tailWord_799011) baseStart_799011 baseEnd_799011 := by
    simpa [prefixWord, tailWord_799011, baseEnd_799011] using wordTrace_append hprefix tailTrace_799011
  have hstable : (prefixWord ++ tailWord_799011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799011).length < 2 ^ (prefixWord ++ tailWord_799011).sum := by decide
  have hdescent : baseEnd_799011 < baseStart_799011 := by decide
  rcases family_descends (prefixWord ++ tailWord_799011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799072 : List Nat := [2, 1, 1, 3, 6, 1, 1, 2, 6]
def baseStart_799072 : Nat := 118140960795 + 799072 * 2 ^ 59
def prefixEnd_799072 : Nat := 4983230072969 + 3 ^ 40 * 799072 * 2
def baseEnd_799072 : Nat := 45589779283289206758349

theorem tailTrace_799072 : CollatzResearch.WordTrace tailWord_799072 prefixEnd_799072 45589779283289206758349 := by
  unfold tailWord_799072
  simp only [CollatzResearch.WordTrace]
  refine ⟨14572275080553044738863735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19429700107404059651818313 14572275080553044738863735)
  ·
    refine ⟨21858412620829567108295603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14572275080553044738863735 21858412620829567108295603)
    ·
      refine ⟨32787618931244350662443405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21858412620829567108295603 32787618931244350662443405)
      ·
        refine ⟨12295357099216631498416277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32787618931244350662443405 12295357099216631498416277)
        ·
          refine ⟨576344864025779601488263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12295357099216631498416277 576344864025779601488263)
          ·
            refine ⟨864517296038669402232395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 576344864025779601488263 864517296038669402232395)
            ·
              refine ⟨1296775944058004103348593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 864517296038669402232395 1296775944058004103348593)
              ·
                refine ⟨972581958043503077511445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1296775944058004103348593 972581958043503077511445)
                ·
                  refine ⟨45589779283289206758349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 972581958043503077511445 45589779283289206758349)
                  ·
                    rfl

theorem cell23_799072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 2, 6].length) (baseStart_799072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_799072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_799072 prefixEnd_799072 := by exact prefixLift 799072
  have htrace : WordTrace (prefixWord ++ tailWord_799072) baseStart_799072 baseEnd_799072 := by
    simpa [prefixWord, tailWord_799072, baseEnd_799072] using wordTrace_append hprefix tailTrace_799072
  have hstable : (prefixWord ++ tailWord_799072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799072).length < 2 ^ (prefixWord ++ tailWord_799072).sum := by decide
  have hdescent : baseEnd_799072 < baseStart_799072 := by decide
  rcases family_descends (prefixWord ++ tailWord_799072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799075 : List Nat := [1, 1, 1, 5, 2, 1, 2, 1, 4, 3, 2]
def baseStart_799075 : Nat := 118140960795 + 799075 * 2 ^ 59
def prefixEnd_799075 : Nat := 4983230072969 + 3 ^ 40 * 799075 * 2
def baseEnd_799075 : Nat := 410309553991566349087627

theorem tailTrace_799075 : CollatzResearch.WordTrace tailWord_799075 prefixEnd_799075 410309553991566349087627 := by
  unfold tailWord_799075
  simp only [CollatzResearch.WordTrace]
  refine ⟨29144659580095220990086679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19429773053396813993391119 29144659580095220990086679)
  ·
    refine ⟨43716989370142831485130019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29144659580095220990086679 43716989370142831485130019)
    ·
      refine ⟨65575484055214247227695029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43716989370142831485130019 65575484055214247227695029)
      ·
        refine ⟨6147701630176335677596409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65575484055214247227695029 6147701630176335677596409)
        ·
          refine ⟨4610776222632251758197307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6147701630176335677596409 4610776222632251758197307)
          ·
            refine ⟨6916164333948377637295961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4610776222632251758197307 6916164333948377637295961)
            ·
              refine ⟨5187123250461283227971971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6916164333948377637295961 5187123250461283227971971)
              ·
                refine ⟨7780684875691924841957957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5187123250461283227971971 7780684875691924841957957)
                ·
                  refine ⟨1458878414192235907867117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7780684875691924841957957 1458878414192235907867117)
                  ·
                    refine ⟨547079405322088465450169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1458878414192235907867117 547079405322088465450169)
                    ·
                      refine ⟨410309553991566349087627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 547079405322088465450169 410309553991566349087627)
                      ·
                        rfl

theorem cell23_799075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 4, 3, 2].length) (baseStart_799075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_799075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_799075 prefixEnd_799075 := by exact prefixLift 799075
  have htrace : WordTrace (prefixWord ++ tailWord_799075) baseStart_799075 baseEnd_799075 := by
    simpa [prefixWord, tailWord_799075, baseEnd_799075] using wordTrace_append hprefix tailTrace_799075
  have hstable : (prefixWord ++ tailWord_799075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799075).length < 2 ^ (prefixWord ++ tailWord_799075).sum := by decide
  have hdescent : baseEnd_799075 < baseStart_799075 := by decide
  rcases family_descends (prefixWord ++ tailWord_799075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799082 : List Nat := [3, 1, 3, 3, 1, 1, 1, 3, 3, 1, 3]
def baseStart_799082 : Nat := 118140960795 + 799082 * 2 ^ 59
def prefixEnd_799082 : Nat := 4983230072969 + 3 ^ 40 * 799082 * 2
def baseEnd_799082 : Nat := 410313148356147821700095

theorem tailTrace_799082 : CollatzResearch.WordTrace tailWord_799082 prefixEnd_799082 410313148356147821700095 := by
  unfold tailWord_799082
  simp only [CollatzResearch.WordTrace]
  refine ⟨7286228722767465296397875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19429943260713240790394333 7286228722767465296397875)
  ·
    refine ⟨10929343084151197944596813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7286228722767465296397875 10929343084151197944596813)
    ·
      refine ⟨4098503656556699229223805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10929343084151197944596813 4098503656556699229223805)
      ·
        refine ⟨1536938871208762210958927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4098503656556699229223805 1536938871208762210958927)
        ·
          refine ⟨2305408306813143316438391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1536938871208762210958927 2305408306813143316438391)
          ·
            refine ⟨3458112460219714974657587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2305408306813143316438391 3458112460219714974657587)
            ·
              refine ⟨5187168690329572461986381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3458112460219714974657587 5187168690329572461986381)
              ·
                refine ⟨1945188258873589673244893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5187168690329572461986381 1945188258873589673244893)
                ·
                  refine ⟨729445597077596127466835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1945188258873589673244893 729445597077596127466835)
                  ·
                    refine ⟨1094168395616394191200253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 729445597077596127466835 1094168395616394191200253)
                    ·
                      refine ⟨410313148356147821700095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1094168395616394191200253 410313148356147821700095)
                      ·
                        rfl

theorem cell23_799082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_799082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_799082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_799082 prefixEnd_799082 := by exact prefixLift 799082
  have htrace : WordTrace (prefixWord ++ tailWord_799082) baseStart_799082 baseEnd_799082 := by
    simpa [prefixWord, tailWord_799082, baseEnd_799082] using wordTrace_append hprefix tailTrace_799082
  have hstable : (prefixWord ++ tailWord_799082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799082).length < 2 ^ (prefixWord ++ tailWord_799082).sum := by decide
  have hdescent : baseEnd_799082 < baseStart_799082 := by decide
  rcases family_descends (prefixWord ++ tailWord_799082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799098 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 8, 4]
def baseStart_799098 : Nat := 118140960795 + 799098 * 2 ^ 59
def prefixEnd_799098 : Nat := 4983230072969 + 3 ^ 40 * 799098 * 2
def baseEnd_799098 : Nat := 136773788015539919700007

theorem tailTrace_799098 : CollatzResearch.WordTrace tailWord_799098 prefixEnd_799098 136773788015539919700007 := by
  unfold tailWord_799098
  simp only [CollatzResearch.WordTrace]
  refine ⟨7286374614752973979543487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19430332306007930612115965 7286374614752973979543487)
  ·
    refine ⟨10929561922129460969315231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7286374614752973979543487 10929561922129460969315231)
    ·
      refine ⟨16394342883194191453972847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10929561922129460969315231 16394342883194191453972847)
      ·
        refine ⟨24591514324791287180959271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16394342883194191453972847 24591514324791287180959271)
        ·
          refine ⟨36887271487186930771438907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24591514324791287180959271 36887271487186930771438907)
          ·
            refine ⟨55330907230780396157158361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36887271487186930771438907 55330907230780396157158361)
            ·
              refine ⟨41498180423085297117868771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55330907230780396157158361 41498180423085297117868771)
              ·
                refine ⟨62247270634627945676803157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41498180423085297117868771 62247270634627945676803157)
                ·
                  refine ⟨729460202749546238400037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 62247270634627945676803157 729460202749546238400037)
                  ·
                    refine ⟨136773788015539919700007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 729460202749546238400037 136773788015539919700007)
                    ·
                      rfl

theorem cell23_799098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 8, 4].length) (baseStart_799098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_799098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_799098 prefixEnd_799098 := by exact prefixLift 799098
  have htrace : WordTrace (prefixWord ++ tailWord_799098) baseStart_799098 baseEnd_799098 := by
    simpa [prefixWord, tailWord_799098, baseEnd_799098] using wordTrace_append hprefix tailTrace_799098
  have hstable : (prefixWord ++ tailWord_799098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799098).length < 2 ^ (prefixWord ++ tailWord_799098).sum := by decide
  have hdescent : baseEnd_799098 < baseStart_799098 := by decide
  rcases family_descends (prefixWord ++ tailWord_799098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799108 : List Nat := [2, 3, 2, 1, 1, 2, 1, 2, 3, 1, 5]
def baseStart_799108 : Nat := 118140960795 + 799108 * 2 ^ 59
def prefixEnd_799108 : Nat := 4983230072969 + 3 ^ 40 * 799108 * 2
def baseEnd_799108 : Nat := 410326498853164719974975

theorem tailTrace_799108 : CollatzResearch.WordTrace tailWord_799108 prefixEnd_799108 410326498853164719974975 := by
  unfold tailWord_799108
  simp only [CollatzResearch.WordTrace]
  refine ⟨14572931594487833813018989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19430575459317111750691985 14572931594487833813018989)
  ·
    refine ⟨5464849347932937679882121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14572931594487833813018989 5464849347932937679882121)
    ·
      refine ⟨4098637010949703259911591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5464849347932937679882121 4098637010949703259911591)
      ·
        refine ⟨6147955516424554889867387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4098637010949703259911591 6147955516424554889867387)
        ·
          refine ⟨9221933274636832334801081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6147955516424554889867387 9221933274636832334801081)
          ·
            refine ⟨6916449955977624251100811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9221933274636832334801081 6916449955977624251100811)
            ·
              refine ⟨10374674933966436376651217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6916449955977624251100811 10374674933966436376651217)
              ·
                refine ⟨7781006200474827282488413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10374674933966436376651217 7781006200474827282488413)
                ·
                  refine ⟨2917877325178060230933155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7781006200474827282488413 2917877325178060230933155)
                  ·
                    refine ⟨4376815987767090346399733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2917877325178060230933155 4376815987767090346399733)
                    ·
                      refine ⟨410326498853164719974975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4376815987767090346399733 410326498853164719974975)
                      ·
                        rfl

theorem cell23_799108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_799108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_799108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_799108 prefixEnd_799108 := by exact prefixLift 799108
  have htrace : WordTrace (prefixWord ++ tailWord_799108) baseStart_799108 baseEnd_799108 := by
    simpa [prefixWord, tailWord_799108, baseEnd_799108] using wordTrace_append hprefix tailTrace_799108
  have hstable : (prefixWord ++ tailWord_799108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799108).length < 2 ^ (prefixWord ++ tailWord_799108).sum := by decide
  have hdescent : baseEnd_799108 < baseStart_799108 := by decide
  rcases family_descends (prefixWord ++ tailWord_799108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799128 : List Nat := [2, 1, 2, 5, 1, 1, 11]
def baseStart_799128 : Nat := 118140960795 + 799128 * 2 ^ 59
def prefixEnd_799128 : Nat := 4983230072969 + 3 ^ 40 * 799128 * 2
def baseEnd_799128 : Nat := 5065886030447588169443

theorem tailTrace_799128 : CollatzResearch.WordTrace tailWord_799128 prefixEnd_799128 5065886030447588169443 := by
  unfold tailWord_799128
  simp only [CollatzResearch.WordTrace]
  refine ⟨14573296324451605520883019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19431061765935474027844025 14573296324451605520883019)
  ·
    refine ⟨21859944486677408281324529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14573296324451605520883019 21859944486677408281324529)
    ·
      refine ⟨16394958365008056210993397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21859944486677408281324529 16394958365008056210993397)
      ·
        refine ⟨1537027346719505269780631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16394958365008056210993397 1537027346719505269780631)
        ·
          refine ⟨2305541020079257904670947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1537027346719505269780631 2305541020079257904670947)
          ·
            refine ⟨3458311530118886857006421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2305541020079257904670947 3458311530118886857006421)
            ·
              refine ⟨5065886030447588169443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 3458311530118886857006421 5065886030447588169443)
              ·
                rfl

theorem cell23_799128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 11].length) (baseStart_799128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_799128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_799128 prefixEnd_799128 := by exact prefixLift 799128
  have htrace : WordTrace (prefixWord ++ tailWord_799128) baseStart_799128 baseEnd_799128 := by
    simpa [prefixWord, tailWord_799128, baseEnd_799128] using wordTrace_append hprefix tailTrace_799128
  have hstable : (prefixWord ++ tailWord_799128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799128).length < 2 ^ (prefixWord ++ tailWord_799128).sum := by decide
  have hdescent : baseEnd_799128 < baseStart_799128 := by decide
  rcases family_descends (prefixWord ++ tailWord_799128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799139 : List Nat := [1, 1, 1, 4, 1, 6, 1, 1, 3, 2, 2]
def baseStart_799139 : Nat := 118140960795 + 799139 * 2 ^ 59
def prefixEnd_799139 : Nat := 4983230072969 + 3 ^ 40 * 799139 * 2
def baseEnd_799139 : Nat := 410342416753454098687333

theorem tailTrace_799139 : CollatzResearch.WordTrace tailWord_799139 prefixEnd_799139 410342416753454098687333 := by
  unfold tailWord_799139
  simp only [CollatzResearch.WordTrace]
  refine ⟨29146993851863359920416471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19431329234575573280277647 29146993851863359920416471)
  ·
    refine ⟨43720490777795039880624707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29146993851863359920416471 43720490777795039880624707)
    ·
      refine ⟨65580736166692559820937061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43720490777795039880624707 65580736166692559820937061)
      ·
        refine ⟨12296388031254854966425699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65580736166692559820937061 12296388031254854966425699)
        ·
          refine ⟨18444582046882282449638549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12296388031254854966425699 18444582046882282449638549)
          ·
            refine ⟨864589783447606989826807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 18444582046882282449638549 864589783447606989826807)
            ·
              refine ⟨1296884675171410484740211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 864589783447606989826807 1296884675171410484740211)
              ·
                refine ⟨1945327012757115727110317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1296884675171410484740211 1945327012757115727110317)
                ·
                  refine ⟨729497629783918397666369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1945327012757115727110317 729497629783918397666369)
                  ·
                    refine ⟨547123222337938798249777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 729497629783918397666369 547123222337938798249777)
                    ·
                      refine ⟨410342416753454098687333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 547123222337938798249777 410342416753454098687333)
                      ·
                        rfl

theorem cell23_799139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 1, 3, 2, 2].length) (baseStart_799139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_799139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_799139 prefixEnd_799139 := by exact prefixLift 799139
  have htrace : WordTrace (prefixWord ++ tailWord_799139) baseStart_799139 baseEnd_799139 := by
    simpa [prefixWord, tailWord_799139, baseEnd_799139] using wordTrace_append hprefix tailTrace_799139
  have hstable : (prefixWord ++ tailWord_799139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799139).length < 2 ^ (prefixWord ++ tailWord_799139).sum := by decide
  have hdescent : baseEnd_799139 < baseStart_799139 := by decide
  rcases family_descends (prefixWord ++ tailWord_799139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799149 : List Nat := [1, 5, 2, 2, 2, 1, 1, 3, 2, 4]
def baseStart_799149 : Nat := 118140960795 + 799149 * 2 ^ 59
def prefixEnd_799149 : Nat := 4983230072969 + 3 ^ 40 * 799149 * 2
def baseEnd_799149 : Nat := 136782517186666353187429

theorem tailTrace_799149 : CollatzResearch.WordTrace tailWord_799149 prefixEnd_799149 136782517186666353187429 := by
  unfold tailWord_799149
  simp only [CollatzResearch.WordTrace]
  refine ⟨29147358581827131628280501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19431572387884754418853667 29147358581827131628280501)
  ·
    refine ⟨2732564867046293590151297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29147358581827131628280501 2732564867046293590151297)
    ·
      refine ⟨2049423650284720192613473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2732564867046293590151297 2049423650284720192613473)
      ·
        refine ⟨1537067737713540144460105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2049423650284720192613473 1537067737713540144460105)
        ·
          refine ⟨1152800803285155108345079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1537067737713540144460105 1152800803285155108345079)
          ·
            refine ⟨1729201204927732662517619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1152800803285155108345079 1729201204927732662517619)
            ·
              refine ⟨2593801807391598993776429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1729201204927732662517619 2593801807391598993776429)
              ·
                refine ⟨972675677771849622666161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2593801807391598993776429 972675677771849622666161)
                ·
                  refine ⟨729506758328887216999621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 972675677771849622666161 729506758328887216999621)
                  ·
                    refine ⟨136782517186666353187429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 729506758328887216999621 136782517186666353187429)
                    ·
                      rfl

theorem cell23_799149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_799149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_799149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_799149 prefixEnd_799149 := by exact prefixLift 799149
  have htrace : WordTrace (prefixWord ++ tailWord_799149) baseStart_799149 baseEnd_799149 := by
    simpa [prefixWord, tailWord_799149, baseEnd_799149] using wordTrace_append hprefix tailTrace_799149
  have hstable : (prefixWord ++ tailWord_799149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799149).length < 2 ^ (prefixWord ++ tailWord_799149).sum := by decide
  have hdescent : baseEnd_799149 < baseStart_799149 := by decide
  rcases family_descends (prefixWord ++ tailWord_799149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
